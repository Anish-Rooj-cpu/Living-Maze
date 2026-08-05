(function(){
  "use strict";

  // ---------- config ----------
  const N = 25;                 
  const CELL = 22;               
  const PADDING = 4;
  const CANVAS_SIZE = N * CELL + PADDING * 2;

  const DIRS = ['N','E','S','W'];
  const OPP = { N:'S', S:'N', E:'W', W:'E' };
  const DELTA = { N:[-1,0], S:[1,0], E:[0,1], W:[0,-1] };

  let TICK_BASE = 3000;     // ms between natural shifts
  let TICK_MIN  = 1200;
  let tickInterval = TICK_BASE;
  let enemySpeed = 1;      // cells pursuer advances per shift
  const STALL_LIMIT = 1500; // ms idle before forced shift

  // ---------- state ----------
  let walls;             
  let targetWalls = null; 
  let shiftAnimStart = 0;
  const SHIFT_DURATION = 300;

  let player, exitCell, start;
  let zombieA, zombieB;
  let zombieBActive = false;

  let moveCount = 0, shiftCount = 0;
  let startTime = 0, elapsed = 0;
  let running = false, won = false, lost = false;
  let lastMoveAt = 0;
  let lastActualMove = 0; 
  const MOVE_COOLDOWN = 60;

  // Fading trails
  let collapsedTiles = []; // {r, c, expire}
  const COLLAPSE_DURATION = 4000; 

  let autoPilotActive = false;
  let solutionCooldownUntil = 0;
  const SOLUTION_COOLDOWN_MS = 5000;

  let tickTimer = null, tickStartedAt = 0, tickDuration = tickInterval;

  // visual positions
  let playerPix, zAPix, zBPix;

  // ---------- dom ----------
  const canvas = document.getElementById('game');
  const ctx = canvas.getContext('2d');
  canvas.width = CANVAS_SIZE;
  canvas.height = CANVAS_SIZE;

  const overlay = document.getElementById('overlay');
  const startBtn = document.getElementById('startBtn');
  const restartBtn = document.getElementById('restartBtn');
  const solutionBtn = document.getElementById('solutionBtn');
  const tickBar = document.getElementById('tickBar');
  const msgEl = document.getElementById('msg');

  const statTime = document.getElementById('statTime');
  const statMoves = document.getElementById('statMoves');
  const statShifts = document.getElementById('statShifts');
  const statDist = document.getElementById('statDist');
  const statSpeed = document.getElementById('statSpeed');

  // ---------- utils ----------
  function randInt(min, max){ return Math.floor(Math.random() * (max - min + 1)) + min; }
  function shuffle(arr){
    for(let i=arr.length-1;i>0;i--){
      const j = randInt(0,i);
      [arr[i],arr[j]] = [arr[j],arr[i]];
    }
    return arr;
  }
  function inBounds(r,c){ return r>=0 && r<N && c>=0 && c<N; }
  function neighborCoord(r,c,dir){ const [dr,dc]=DELTA[dir]; return [r+dr, c+dc]; }
  function key(r,c){ return r*N+c; }

  function flashMsg(text, ms){
    msgEl.textContent = text;
    msgEl.classList.add('show');
    clearTimeout(flashMsg._t);
    flashMsg._t = setTimeout(()=> msgEl.classList.remove('show'), ms || 1100);
  }

  function cloneWalls(w) {
    return w.map(row => row.map(cell => ({...cell})));
  }

  // ---------- maze generation ----------
  function initWalls(){
    const w = [];
    for(let r=0;r<N;r++){
      const row = [];
      for(let c=0;c<N;c++) row.push({N:true,E:true,S:true,W:true});
      w.push(row);
    }
    return w;
  }

  function setWallIn(w, r, c, dir, value){
    w[r][c][dir] = value;
    const [nr,nc] = neighborCoord(r,c,dir);
    if(inBounds(nr,nc)) w[nr][nc][OPP[dir]] = value;
  }

  function generatePerfectMaze(startR, startC){
    const w = initWalls();
    const visited = Array.from({length:N}, ()=> new Array(N).fill(false));
    const stack = [[startR, startC]];
    visited[startR][startC] = true;
    
    while(stack.length){
      const [r,c] = stack[stack.length-1];
      const dirs = shuffle(DIRS.slice());
      let moved = false;
      for(const dir of dirs){
        const [nr,nc] = neighborCoord(r,c,dir);
        if(inBounds(nr,nc) && !visited[nr][nc]){
          setWallIn(w, r, c, dir, false);
          visited[nr][nc] = true;
          stack.push([nr,nc]);
          moved = true;
          break;
        }
      }
      if(!moved) stack.pop();
    }
    return w;
  }

  function braidMaze(w, count){
    let removed = 0;
    let attempts = 0;
    while(removed < count && attempts < count * 5){
      attempts++;
      const r = randInt(0, N-1);
      const c = randInt(0, N-1);
      const dir = DIRS[randInt(0,3)];
      if(w[r][c][dir]){
        const [nr,nc] = neighborCoord(r,c,dir);
        if(inBounds(nr,nc)){
          setWallIn(w, r, c, dir, false);
          removed++;
        }
      }
    }
  }

  function getPathEdges(path) {
    const edges = [];
    for(let i = 0; i < path.length - 1; i++) {
      const a = path[i];
      const b = path[i+1];
      let dir;
      if(b.r < a.r) dir = 'N';
      else if(b.r > a.r) dir = 'S';
      else if(b.c > a.c) dir = 'E';
      else if(b.c < a.c) dir = 'W';
      edges.push({r: a.r, c: a.c, dir});
    }
    return edges;
  }

  // Smooth, Proactive Mutation
  function mutateMazeProactively(currentWalls, isForced){
    const w = cloneWalls(currentWalls);

    if (isForced) {
      for(const h of [zombieA, zombieBActive ? zombieB : null]) {
        if(!h) continue;
        let bestDir = null;
        let minDist = bfsDist(w, h.r, h.c, player.r, player.c);
        for(const dir of DIRS) {
          if(w[h.r][h.c][dir]) { 
            const [nr,nc] = neighborCoord(h.r, h.c, dir);
            if(inBounds(nr,nc)) {
              setWallIn(w, h.r, h.c, dir, false);
              const d = bfsDist(w, nr, nc, player.r, player.c);
              if(d < minDist) {
                minDist = d;
                bestDir = dir;
              }
              setWallIn(w, h.r, h.c, dir, true); 
            }
          }
        }
        if(bestDir) {
          setWallIn(w, h.r, h.c, bestDir, false);
        }
      }
    }

    const pPath = bfsPath(w, player.r, player.c, exitCell.r, exitCell.c);
    if (pPath && pPath.length > 3) {
      const edges = getPathEdges(pPath);
      const targetIdx = Math.min(edges.length - 1, randInt(1, 4));
      const edge = edges[targetIdx];
      
      let opened = 0;
      let attempts = 0;
      while(opened < 2 && attempts < 40) {
        attempts++;
        const r = randInt(0, N-1), c = randInt(0, N-1), dir = DIRS[randInt(0,3)];
        if (w[r][c][dir]) {
          const [nr,nc] = neighborCoord(r,c,dir);
          if (inBounds(nr,nc)) {
            setWallIn(w, r, c, dir, false);
            opened++;
          }
        }
      }

      setWallIn(w, edge.r, edge.c, edge.dir, true);
      if (!bfsPath(w, player.r, player.c, exitCell.r, exitCell.c)) {
        setWallIn(w, edge.r, edge.c, edge.dir, false);
      }
    }

    for(let i=0; i<3; i++) {
      let r = randInt(0, N-1), c = randInt(0, N-1), dir = DIRS[randInt(0,3)];
      if(w[r][c][dir]) {
        const [nr,nc] = neighborCoord(r,c,dir);
        if (inBounds(nr,nc)) setWallIn(w, r, c, dir, false);
      }
      
      r = randInt(0, N-1); c = randInt(0, N-1); dir = DIRS[randInt(0,3)];
      if(!w[r][c][dir]) {
        const [nr,nc] = neighborCoord(r,c,dir);
        if (inBounds(nr,nc)) {
          setWallIn(w, r, c, dir, true);
          if(!bfsPath(w, player.r, player.c, exitCell.r, exitCell.c)) {
            setWallIn(w, r, c, dir, false); 
          }
        }
      }
    }

    return w;
  }

  // ---------- pathfinding ----------
  function openNeighbors(w, r, c){
    const out = [];
    for(const dir of DIRS){
      if(!w[r][c][dir]){
        const [nr,nc] = neighborCoord(r,c,dir);
        if(inBounds(nr,nc)){
          out.push({r:nr,c:nc,dir});
        }
      }
    }
    return out;
  }

  function bfsPath(w, sr, sc, er, ec){
    if(sr===er && sc===ec) return [{r:sr,c:sc}];
    const prev = new Array(N*N).fill(-1);
    const visited = new Array(N*N).fill(false);
    const q = [[sr,sc]];
    visited[key(sr,sc)] = true;
    let found = false;
    
    while(q.length){
      const [r,c] = q.shift();
      if(r===er && c===ec){ found = true; break; }
      for(const nb of openNeighbors(w, r, c)){
        const k = key(nb.r,nb.c);
        if(!visited[k]){
          visited[k] = true;
          prev[k] = key(r,c);
          q.push([nb.r,nb.c]);
        }
      }
    }
    if(!found) return null;
    const path = [];
    let cur = key(er,ec);
    while(cur !== -1){
      const r = Math.floor(cur / N), c = cur % N;
      path.push({r,c});
      if(r===sr && c===sc) break;
      cur = prev[cur];
    }
    path.reverse();
    return path;
  }

  function bfsDist(w, sr, sc, er, ec){
    const p = bfsPath(w, sr, sc, er, ec);
    return p ? p.length - 1 : Infinity;
  }

  function getBestMove() {
    const dangerMap = new Array(N*N).fill(Infinity);
    for(let r=0; r<N; r++){
      for(let c=0; c<N; c++){
        const dA = bfsDist(walls, zombieA.r, zombieA.c, r, c);
        const dB = zombieBActive ? bfsDist(walls, zombieB.r, zombieB.c, r, c) : Infinity;
        dangerMap[key(r,c)] = Math.min(dA, dB);
      }
    }

    const dist = new Array(N*N).fill(Infinity);
    const prev = new Array(N*N).fill(-1);
    const pq = [{k: key(player.r, player.c), cost: 0}];
    dist[pq[0].k] = 0;
    const visited = new Array(N*N).fill(false);
    
    while(pq.length > 0) {
      pq.sort((a,b) => a.cost - b.cost);
      const {k, cost} = pq.shift();
      if (visited[k]) continue;
      visited[k] = true;
      
      const r = Math.floor(k/N), c = k%N;
      if (r === exitCell.r && c === exitCell.c) break;

      for(const nb of openNeighbors(walls, r, c)) {
        const nk = key(nb.r, nb.c);
        if(visited[nk]) continue;
        
        let penalty = 1;
        if (isCollapsed(nb.r, nb.c)) penalty += 200; 
        
        const danger = dangerMap[nk];
        if (danger === 0) penalty += 10000; 
        else if (danger === 1) penalty += 1000; 
        else if (danger === 2) penalty += 100;
        else if (danger === 3) penalty += 20;

        const newCost = cost + penalty;
        if (newCost < dist[nk]) {
          dist[nk] = newCost;
          prev[nk] = k;
          pq.push({k: nk, cost: newCost});
        }
      }
    }
    
    let cur = key(exitCell.r, exitCell.c);
    if (prev[cur] !== -1) {
      const path = [];
      while(cur !== -1) {
        const r = Math.floor(cur / N), c = cur % N;
        path.push({r,c});
        if(r===player.r && c===player.c) break;
        cur = prev[cur];
      }
      path.reverse();
      
      if (path.length > 1) {
        const next = path[1];
        if (dangerMap[key(next.r, next.c)] <= 1) {
          return getSurvivalMove(dangerMap);
        }
        if (next.r < player.r) return 'N';
        if (next.r > player.r) return 'S';
        if (next.c > player.c) return 'E';
        if (next.c < player.c) return 'W';
      }
    }

    return getSurvivalMove(dangerMap);
  }

  function getSurvivalMove(dangerMap) {
    let bestDir = null;
    let bestScore = dangerMap[key(player.r, player.c)]; 
    
    for(const nb of openNeighbors(walls, player.r, player.c)) {
      let score = dangerMap[key(nb.r, nb.c)];
      if (isCollapsed(nb.r, nb.c)) score -= 5; 
      
      if (score > bestScore) {
        bestScore = score;
        bestDir = nb.dir;
      }
    }
    return bestDir;
  }

  // ---------- trails ----------
  function isCollapsed(r,c){
    const now = performance.now();
    for(const t of collapsedTiles){
      if(t.r === r && t.c === c && now < t.expire) return true;
    }
    return false;
  }

  function cleanTrails(now){
    collapsedTiles = collapsedTiles.filter(t => now < t.expire);
  }

  // ---------- enemy ----------
  function moveEnemy(enemyObj, targetR, targetC){
    for(let s=0; s<enemySpeed; s++){
      const path = bfsPath(walls, enemyObj.r, enemyObj.c, targetR, targetC);
      if(!path || path.length <= 1) break;
      enemyObj.r = path[1].r;
      enemyObj.c = path[1].c;
      if(enemyObj.r === targetR && enemyObj.c === targetC) break;
    }
  }

  function moveEnemies(){
    moveEnemy(zombieA, player.r, player.c);

    if(zombieBActive){
      const pPath = bfsPath(walls, player.r, player.c, exitCell.r, exitCell.c);
      let targetR = player.r, targetC = player.c;
      if(pPath && pPath.length > 5){
        targetR = pPath[4].r;
        targetC = pPath[4].c;
      }
      moveEnemy(zombieB, targetR, targetC);
    }
  }

  // ---------- game flow ----------
  function placeActors(){
    start = {r:0,c:0};
    exitCell = {r:N-1,c:N-1};
    walls = generatePerfectMaze(0, 0);
    braidMaze(walls, 40);

    zombieA = {r:0,c:0};
    const pPath = bfsPath(walls, 0, 0, exitCell.r, exitCell.c);
    if(pPath && pPath.length > 1){
      player = {r:pPath[1].r, c:pPath[1].c};
    } else {
      player = {r:0,c:0};
    }

    zombieB = {r:0,c:N-1}; 
    zombieBActive = false;

    playerPix = {x:PADDING + player.c*CELL, y:PADDING + player.r*CELL};
    zAPix = {x:PADDING + zombieA.c*CELL, y:PADDING + zombieA.r*CELL};
    zBPix = {x:PADDING + zombieB.c*CELL, y:PADDING + zombieB.r*CELL};
  }

  function resetGame(){
    placeActors();
    moveCount = 0; shiftCount = 0; elapsed = 0;
    tickInterval = TICK_BASE;
    enemySpeed = 1;
    won = false; lost = false; running = false;
    autoPilotActive = false;
    solutionCooldownUntil = 0;
    collapsedTiles = [];
    solutionBtn.disabled = false;
    solutionBtn.textContent = 'Auto-Pilot';
    solutionBtn.style.boxShadow = '';
    lastActualMove = performance.now();
    updateHud();
    drawMaze(performance.now());
    drawActors();
  }

  function startGame(){
    resetGame();
    running = true;
    const now = performance.now();
    startTime = now;
    lastActualMove = now;
    overlay.classList.add('hidden');
    scheduleTick();
    flashMsg('THE MAZE IS ALIVE', 1400);
  }

  function endGame(didWin){
    running = false;
    autoPilotActive = false;
    solutionBtn.textContent = 'Auto-Pilot';
    solutionBtn.style.boxShadow = '';
    won = didWin; lost = !didWin;
    clearTimeout(tickTimer);
    overlay.classList.remove('hidden');
    document.body.classList.remove('stress');
    if(didWin){
      overlay.innerHTML = `
        <h2 class="glow-gold">You Cleared the Shift</h2>
        <p>You crossed <b class="glow-gold">${moveCount}</b> steps and endured <b class="glow-gold">${shiftCount}</b> shifts of the maze in <b class="glow-gold">${(elapsed/1000).toFixed(1)}s</b>.</p>
        <button id="startBtn2">Escape Again</button>
      `;
    } else {
      overlay.innerHTML = `
        <h2 class="glow-blood">Caught in the Turning Walls</h2>
        <p>You held out for <b class="glow-blood">${(elapsed/1000).toFixed(1)}s</b> across <b class="glow-blood">${shiftCount}</b> shifts before it found you.</p>
        <button id="startBtn2">Try Again</button>
      `;
    }
    document.getElementById('startBtn2').addEventListener('click', startGame);
  }

  function checkCollision(){
    if((player.r === zombieA.r && player.c === zombieA.c) || 
       (zombieBActive && player.r === zombieB.r && player.c === zombieB.c)){
      endGame(false);
      return true;
    }
    return false;
  }

  function checkWin(){
    if(player.r === exitCell.r && player.c === exitCell.c){
      endGame(true);
      return true;
    }
    return false;
  }

  // ---------- input ----------
  const KEYMAP = {
    ArrowUp:'N', ArrowDown:'S', ArrowLeft:'W', ArrowRight:'E',
    w:'N', s:'S', a:'W', d:'E', W:'N', S:'S', A:'W', D:'E'
  };

  function attemptMove(dir, isAutoPilot = false){
    if(!running) return;
    const now = performance.now();
    if(now - lastMoveAt < MOVE_COOLDOWN) return;
    
    if(!isAutoPilot) {
      lastActualMove = now; // Reset anti-stall only for human
      if (autoPilotActive) {
        autoPilotActive = false;
        solutionBtn.textContent = 'Auto-Pilot';
        solutionBtn.style.boxShadow = '';
        flashMsg('MANUAL CONTROL RESUMED', 1200);
      }
    } else {
      // Auto-pilot acts perfectly, shouldn't trigger anti-stall penalty.
      lastActualMove = now; 
    }

    if(walls[player.r][player.c][dir]) return; // blocked by wall
    
    const [nr,nc] = neighborCoord(player.r, player.c, dir);
    if(!inBounds(nr,nc)) return;
    if(isCollapsed(nr,nc)) {
      if(!isAutoPilot) {
        flashMsg('BACKTRACKING WAKES THE MAZE', 1200);
        doShift(true);
      } else {
        // Auto-pilot gets penalty too if forced to step on it.
        doShift(true);
      }
    }

    collapsedTiles.push({r: player.r, c: player.c, expire: now + COLLAPSE_DURATION});

    player.r = nr; player.c = nc;
    lastMoveAt = now;
    moveCount++;
    updateHud();

    if(checkCollision()) return;
    if(checkWin()) return;
  }

  window.addEventListener('keydown', (e)=>{
    const dir = KEYMAP[e.key];
    if(dir){
      e.preventDefault();
      attemptMove(dir);
    }
  }, {passive:false});

  // ---------- tick loop (the shift) ----------
  function scheduleTick(){
    tickDuration = tickInterval;
    tickStartedAt = performance.now();
    tickTimer = setTimeout(() => doShift(false), tickInterval);
  }

  function doShift(isForced){
    if(!running) return;
    if(!isForced) clearTimeout(tickTimer);

    targetWalls = mutateMazeProactively(walls, isForced);
    shiftAnimStart = performance.now();
    walls = targetWalls;

    moveEnemies();
    shiftCount++;

    if(shiftCount === 20){
      zombieBActive = true;
      flashMsg('A SECOND HUNTER WAKES', 2000);
    }

    tickInterval = Math.max(TICK_MIN, tickInterval * 0.95);
    if(shiftCount % 12 === 0 && enemySpeed < 2) enemySpeed++;

    updateHud();
    if(checkCollision()) return;

    if(isForced) lastActualMove = performance.now(); 
    scheduleTick();
  }

  // ---------- solution ----------
  function toggleAutoPilot(){
    const now = performance.now();
    if(!running) return;
    
    if(autoPilotActive) {
      autoPilotActive = false;
      solutionBtn.textContent = 'Auto-Pilot';
      solutionBtn.style.boxShadow = '';
      flashMsg('MANUAL CONTROL RESUMED', 1200);
    } else {
      autoPilotActive = true;
      solutionBtn.textContent = 'Auto-Pilot: ON';
      solutionBtn.style.boxShadow = '0 0 20px rgba(100, 200, 255, 0.8)';
      flashMsg('AI TAKING OVER', 1500);
    }
  }

  // ---------- hud & effects ----------
  function updateHud(){
    statMoves.textContent = moveCount;
    statShifts.textContent = shiftCount;
    const dA = bfsDist(walls, zombieA.r, zombieA.c, player.r, player.c);
    const dB = zombieBActive ? bfsDist(walls, zombieB.r, zombieB.c, player.r, player.c) : Infinity;
    const d = Math.min(dA, dB);
    
    statDist.textContent = (d===Infinity) ? '—' : d;
    statDist.style.color = (d!==Infinity && d<=3) ? 'var(--blood-bright)' : '';
    statSpeed.textContent = 'x' + enemySpeed;
    statSpeed.style.color = enemySpeed >= 2 ? 'var(--blood-bright)' : '';
    
    updateStress(d);
  }

  function updateStress(dist){
    if(dist <= 4) {
      document.body.classList.add('stress');
    } else {
      document.body.classList.remove('stress');
    }
  }

  // ---------- render ----------
  function drawWalls(w, alpha){
    ctx.strokeStyle = `rgba(74, 58, 38, ${alpha})`;
    ctx.lineWidth = 2.5;
    ctx.lineCap = 'round';
    for(let r=0;r<N;r++){
      for(let c=0;c<N;c++){
        const x0 = PADDING + c*CELL, y0 = PADDING + r*CELL;
        const x1 = x0 + CELL, y1 = y0 + CELL;
        const cellW = w[r][c];
        ctx.beginPath();
        if(cellW.N){ ctx.moveTo(x0,y0); ctx.lineTo(x1,y0); }
        if(cellW.W){ ctx.moveTo(x0,y0); ctx.lineTo(x0,y1); }
        if(cellW.S){ ctx.moveTo(x0,y1); ctx.lineTo(x1,y1); }
        if(cellW.E){ ctx.moveTo(x1,y0); ctx.lineTo(x1,y1); }
        ctx.stroke();
      }
    }
  }

  function drawMaze(now){
    ctx.clearRect(0,0,canvas.width,canvas.height);

    ctx.fillStyle = '#100c08';
    ctx.fillRect(0,0,canvas.width,canvas.height);

    ctx.strokeStyle = 'rgba(201,154,74,0.03)';
    ctx.lineWidth = 1;
    for(let i=0;i<=N;i++){
      ctx.beginPath();
      ctx.moveTo(PADDING + i*CELL, PADDING);
      ctx.lineTo(PADDING + i*CELL, PADDING + N*CELL);
      ctx.stroke();
      ctx.beginPath();
      ctx.moveTo(PADDING, PADDING + i*CELL);
      ctx.lineTo(PADDING + N*CELL, PADDING + i*CELL);
      ctx.stroke();
    }
    
    for(const t of collapsedTiles){
      if(now < t.expire){
        const p = (t.expire - now) / COLLAPSE_DURATION; 
        ctx.fillStyle = `rgba(30, 8, 8, ${p * 0.8})`;
        ctx.fillRect(PADDING + t.c*CELL, PADDING + t.r*CELL, CELL, CELL);
      }
    }

    const ex = PADDING + exitCell.c*CELL + CELL/2;
    const ey = PADDING + exitCell.r*CELL + CELL/2;
    const pulse = 0.5 + 0.5*Math.sin(now/260);
    const grad = ctx.createRadialGradient(ex,ey,1,ex,ey,CELL*0.8);
    grad.addColorStop(0, `rgba(240,198,116,${0.4+0.2*pulse})`);
    grad.addColorStop(1, 'rgba(240,198,116,0)');
    ctx.fillStyle = grad;
    ctx.beginPath();
    ctx.arc(ex,ey,CELL*0.8,0,Math.PI*2);
    ctx.fill();
    ctx.strokeStyle = '#f0c674';
    ctx.lineWidth = 1.5;
    ctx.beginPath();
    ctx.arc(ex,ey,CELL*0.3,0,Math.PI*2);
    ctx.stroke();

    let t = (now - shiftAnimStart) / SHIFT_DURATION;
    if(t > 1) t = 1;
    
    if(t < 1 && targetWalls){
      drawWalls(targetWalls, t);
    } else {
      drawWalls(walls, 1);
    }

    ctx.strokeStyle = 'rgba(201,154,74,0.3)';
    ctx.lineWidth = 2;
    ctx.strokeRect(PADDING, PADDING, N*CELL, N*CELL);
  }

  function drawActors(){
    const targetPx = PADDING + player.c*CELL;
    const targetPy = PADDING + player.r*CELL;
    playerPix.x += (targetPx - playerPix.x) * 0.35;
    playerPix.y += (targetPy - playerPix.y) * 0.35;

    const targetAx = PADDING + zombieA.c*CELL;
    const targetAy = PADDING + zombieA.r*CELL;
    zAPix.x += (targetAx - zAPix.x) * 0.22;
    zAPix.y += (targetAy - zAPix.y) * 0.22;

    if(zombieBActive){
      const targetBx = PADDING + zombieB.c*CELL;
      const targetBy = PADDING + zombieB.r*CELL;
      zBPix.x += (targetBx - zBPix.x) * 0.15; 
      zBPix.y += (targetBy - zBPix.y) * 0.15;
    }

    const acx = zAPix.x + CELL/2, acy = zAPix.y + CELL/2;
    const aGrad = ctx.createRadialGradient(acx,acy,1,acx,acy,CELL*0.6);
    aGrad.addColorStop(0, '#ff6a3d');
    aGrad.addColorStop(1, 'rgba(143,29,29,0)');
    ctx.fillStyle = aGrad;
    ctx.beginPath(); ctx.arc(acx,acy,CELL*0.6,0,Math.PI*2); ctx.fill();
    ctx.fillStyle = '#e8402f';
    ctx.beginPath();
    const rotA = performance.now()/400;
    for(let i=0;i<16;i++){
      const r2 = (i%2===0) ? CELL*0.3 : CELL*0.15;
      const ang = rotA + (Math.PI*i)/8;
      if(i===0) ctx.moveTo(acx + Math.cos(ang)*r2, acy + Math.sin(ang)*r2); 
      else ctx.lineTo(acx + Math.cos(ang)*r2, acy + Math.sin(ang)*r2);
    }
    ctx.fill();

    if(zombieBActive){
      const bcx = zBPix.x + CELL/2, bcy = zBPix.y + CELL/2;
      const bGrad = ctx.createRadialGradient(bcx,bcy,1,bcx,bcy,CELL*0.7);
      bGrad.addColorStop(0, '#933dff');
      bGrad.addColorStop(1, 'rgba(46,14,84,0)');
      ctx.fillStyle = bGrad;
      ctx.beginPath(); ctx.arc(bcx,bcy,CELL*0.7,0,Math.PI*2); ctx.fill();
      ctx.fillStyle = '#6b1cb8';
      ctx.beginPath();
      ctx.arc(bcx,bcy,CELL*0.3 + 2*Math.sin(performance.now()/200),0,Math.PI*2);
      ctx.fill();
    }

    const pcx = playerPix.x + CELL/2, pcy = playerPix.y + CELL/2;
    
    // Auto-pilot aura
    if (autoPilotActive) {
      const pGrad = ctx.createRadialGradient(pcx,pcy,1,pcx,pcy,CELL*0.7);
      pGrad.addColorStop(0, '#ffffff');
      pGrad.addColorStop(1, 'rgba(100,200,255,0)');
      ctx.fillStyle = pGrad;
      ctx.beginPath(); ctx.arc(pcx,pcy,CELL*0.7,0,Math.PI*2); ctx.fill();
      ctx.fillStyle = '#b3e0ff';
      ctx.beginPath(); ctx.arc(pcx,pcy,CELL*0.25,0,Math.PI*2); ctx.fill();
    } else {
      const pGrad = ctx.createRadialGradient(pcx,pcy,1,pcx,pcy,CELL*0.5);
      pGrad.addColorStop(0, '#fff2cf');
      pGrad.addColorStop(1, 'rgba(240,198,116,0)');
      ctx.fillStyle = pGrad;
      ctx.beginPath(); ctx.arc(pcx,pcy,CELL*0.5,0,Math.PI*2); ctx.fill();
      ctx.fillStyle = '#f0c674';
      ctx.strokeStyle = '#8a6a2f';
      ctx.lineWidth = 1;
      ctx.beginPath(); ctx.arc(pcx,pcy,CELL*0.22,0,Math.PI*2); ctx.fill(); ctx.stroke();
    }
  }

  function frame(){
    const now = performance.now();
    cleanTrails(now);

    // Auto-Pilot Execution
    if (autoPilotActive && running) {
      if (now - lastMoveAt >= 150) { 
        const bestDir = getBestMove();
        if (bestDir) {
          attemptMove(bestDir, true);
        }
      }
    }

    drawMaze(now);
    drawActors();

    if(running){
      elapsed = now - startTime;
      statTime.textContent = (elapsed/1000).toFixed(1) + 's';

      const tElapsed = now - tickStartedAt;
      const pct = Math.min(1, tElapsed / tickDuration);
      tickBar.style.width = (pct*100).toFixed(1) + '%';

      if(!autoPilotActive && (now - lastActualMove > STALL_LIMIT)){
        flashMsg('THE MAZE PUNISHES HESITATION', 1200);
        doShift(true); 
      }
    }
    requestAnimationFrame(frame);
  }

  // ---------- wire up ----------
  startBtn.addEventListener('click', startGame);
  restartBtn.addEventListener('click', ()=>{
    clearTimeout(tickTimer);
    startGame();
  });
  solutionBtn.addEventListener('click', toggleAutoPilot);

  resetGame();
  requestAnimationFrame(frame);

})();
