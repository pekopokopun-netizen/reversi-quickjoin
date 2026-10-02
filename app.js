(() => {
'use strict';

const SERVICE = '7c2d5a11-4f8e-4a98-9e1c-4f4b5a1e0001';
const RX = '7c2d5a11-4f8e-4a98-9e1c-4f4b5a1e0002';
const TX = '7c2d5a11-4f8e-4a98-9e1c-4f4b5a1e0003';
const PROTOCOL_VERSION = 6;
const Message = { JoinRequest:1, JoinAccepted:2, LobbyState:3, Rules:4, Ready:5, Start:6, Move:7, GameEnd:8, Disconnect:9, SnapshotRequest:10, Snapshot:11, Stamp:12, ConsensusRequest:13, ConsensusVote:14, ConsensusCommit:15 };
const AbilityNames = ['敵駒消去','二連続配置','十字変換','周囲変換','障害物配置','予約','自駒移動','リスク二連','自由配置'];
const ModeNames = ['通常対戦','負けオセロ','爆弾オセロ','障害物オセロ','ポイントオセロ','拡張オセロ','ミックスモード'];
const DiscNames = ['','黒','白','赤','青'];

const $ = id => document.getElementById(id);
let room = (new URL(location.href).searchParams.get('room') || '').replace(/\D/g,'').slice(0,6);
$('room').textContent = `合言葉 ${room || '------'}`;

let transport = null, seq = 1, frameId = 1, localSeat = -1, lobby = null, rules = null, matchId = 0, moveNumber = 0;
let currentState = null, pointActions = null, selectedPointSlot = -1, ready = false;
let joinToken = `QW1:${randomHex(12)}`;
const assemblies = new Map();

class Writer {
  constructor(){ this.a=[]; }
  u8(v){this.a.push(v&255)} i8(v){this.a.push(v&255)} bool(v){this.u8(v?1:0)}
  u16(v){this.u8(v);this.u8(v>>8)} u32(v){v>>>=0;this.u8(v);this.u8(v>>8);this.u8(v>>16);this.u8(v>>24)}
  i32(v){this.u32(v>>>0)}
  str(s){const b=new TextEncoder().encode(s||'');this.u16(b.length);this.bytesRaw(b)}
  bytes(b){b=b||new Uint8Array();this.u16(b.length);this.bytesRaw(b)}
  bytesRaw(b){for(const x of b)this.u8(x)}
  finish(){return new Uint8Array(this.a)}
}
class Reader {
  constructor(bytes){this.b=bytes instanceof Uint8Array?bytes:new Uint8Array(bytes);this.p=0}
  need(n){if(this.p+n>this.b.length)throw new Error('受信データが途中で切れています')}
  u8(){this.need(1);return this.b[this.p++]}
  i8(){const v=this.u8();return v>127?v-256:v}
  bool(){return this.u8()!==0}
  u16(){const a=this.u8(),b=this.u8();return a|(b<<8)}
  u32(){return (this.u8()|(this.u8()<<8)|(this.u8()<<16)|(this.u8()<<24))>>>0}
  i32(){return this.u32()|0}
  str(){const n=this.u16();this.need(n);const s=new TextDecoder().decode(this.b.slice(this.p,this.p+n));this.p+=n;return s}
  bytes(){const n=this.u16();this.need(n);const out=this.b.slice(this.p,this.p+n);this.p+=n;return out}
  raw(n){this.need(n);const out=this.b.slice(this.p,this.p+n);this.p+=n;return out}
  remaining(){return this.b.length-this.p}
}

function writeRules(w,r){
  r=r||{}; w.i32(r.revision||0); w.u8(r.modeIndex||0); w.u8(r.mixModeAIndex||1); w.u8(r.mixModeBIndex||2); w.u8(r.participantCount||2); w.u8(r.boardSize||8); w.i32(r.totalTimeSeconds||0); w.i32(r.resetTimeSeconds||0); w.u8(r.detailIndex||0); w.bool(!!r.allowUndo); w.u8(r.bombExplosionRadius||1); w.u8(r.bombGenerationInterval||0); w.u8(r.obstacleCount||0); w.u8(r.expansionTurns||30);
  for(let i=0;i<4;i++)w.u8((r.pointCosts||[5,10,15,20])[i]||0); for(let i=0;i<4;i++)w.u8((r.pointAbilities||[0,1,2,3])[i]||0); w.bool(!!r.randomOrder); w.u8(r.firstPlayerSlot||0); for(let i=0;i<4;i++)w.u8((r.participantTypes||[0,0,0,0])[i]||0); for(let i=0;i<4;i++)w.u8((r.aiStrengths||[1,1,1,1])[i]||0); for(let i=0;i<4;i++)w.u8((r.fixedOrderPositions||[0,1,2,3])[i]||0);
}
function readRules(r){
  const x={revision:r.i32(),modeIndex:r.u8(),mixModeAIndex:r.u8(),mixModeBIndex:r.u8(),participantCount:r.u8(),boardSize:r.u8(),totalTimeSeconds:r.i32(),resetTimeSeconds:r.i32(),detailIndex:r.u8(),allowUndo:r.bool(),bombExplosionRadius:r.u8(),bombGenerationInterval:r.u8(),obstacleCount:r.u8(),expansionTurns:r.u8(),pointCosts:[],pointAbilities:[],participantTypes:[],aiStrengths:[],fixedOrderPositions:[]};
  for(let i=0;i<4;i++)x.pointCosts.push(r.u8()); for(let i=0;i<4;i++)x.pointAbilities.push(r.u8()); x.randomOrder=r.bool(); x.firstPlayerSlot=r.u8(); for(let i=0;i<4;i++)x.participantTypes.push(r.u8()); for(let i=0;i<4;i++)x.aiStrengths.push(r.u8()); for(let i=0;i<4;i++)x.fixedOrderPositions.push(r.u8()); return x;
}
function readLobby(r){return {roomCode:r.str(),connectedMask:r.u8(),readyMask:r.u8(),localSeat:r.i8(),rules:readRules(r)}}

function encodeMessage(type, fill){
  const w=new Writer();w.u8(PROTOCOL_VERSION);w.u8(type);w.u32(seq++);w.u8(localSeat<0?255:localSeat);w.u8(type===Message.JoinRequest?0:0);if(fill)fill(w);return w.finish();
}
function sendJoin(){sendPayload(encodeMessage(Message.JoinRequest,w=>{w.str(room);w.str(joinToken)}))}
function sendReady(value){sendPayload(encodeMessage(Message.Ready,w=>w.bool(value)))}
function sendMove(a){sendPayload(encodeMessage(Message.Move,w=>{w.u32(matchId);w.u16(moveNumber+1);w.u8(a.row);w.u8(a.col);w.u8(a.kind);w.i8(a.auxRow??-1);w.i8(a.auxCol??-1);w.i8(a.option??-1);w.bool(a.kind===1);w.bytes(new Uint8Array())}))}
function sendSnapshotRequest(extra){sendPayload(encodeMessage(Message.SnapshotRequest,w=>{w.u32(matchId);w.u16(moveNumber);w.bytes(extra||new Uint8Array())}))}
function sendConsensusVote(id,yes){sendPayload(encodeMessage(Message.ConsensusVote,w=>{w.u32(id);w.bool(yes)}))}

async function sendPayload(payload){
  if(!transport) return; const count=Math.max(1,Math.ceil(payload.length/16)); if(count>255) throw new Error('送信データが大きすぎます'); const id=frameId++&0xffff||1;
  for(let i=0;i<count;i++){const part=payload.slice(i*16,Math.min(payload.length,(i+1)*16));const f=new Uint8Array(4+part.length);f[0]=id&255;f[1]=id>>8;f[2]=i;f[3]=count;f.set(part,4);await transport.sendFrame(f)}
}
function receiveFrame(frame){
  if(!(frame instanceof Uint8Array))frame=new Uint8Array(frame);if(frame.length<4)return;const id=frame[0]|(frame[1]<<8),idx=frame[2],count=frame[3];if(!count||idx>=count)return;let a=assemblies.get(id);if(!a||a.parts.length!==count){a={parts:new Array(count),got:0};assemblies.set(id,a)}if(!a.parts[idx]){a.parts[idx]=frame.slice(4);a.got++}if(a.got!==count)return;let n=0;for(const p of a.parts)n+=p.length;const msg=new Uint8Array(n);let o=0;for(const p of a.parts){msg.set(p,o);o+=p.length}assemblies.delete(id);handleMessage(msg)
}

function handleMessage(bytes){
  try{
    const r=new Reader(bytes);const version=r.u8();if(version!==PROTOCOL_VERSION)throw new Error(`通信バージョンが違います (${version})`);const type=r.u8();r.u32();const sender=r.u8(),target=r.u8();if(target!==255&&localSeat>=0&&target!==localSeat)return;
    switch(type){
      case Message.JoinAccepted:{const token=r.str();const seat=r.u8();const l=readLobby(r);if(token!==joinToken)return;localSeat=seat;lobby=l;rules=l.rules;showLobby();status(`プレイヤー${seat+1}として接続しました`);break}
      case Message.LobbyState:lobby=readLobby(r);rules=lobby.rules;showLobby();break;
      case Message.Rules:rules=readRules(r);if(lobby)lobby.rules=rules;ready=false;showLobby();break;
      case Message.Start:matchId=r.u32();rules=readRules(r);const order=r.bytes();$('lobbyCard').classList.add('hidden');$('gameCard').classList.remove('hidden');status('対局を同期しています…');setTimeout(()=>sendSnapshotRequest(),80);break;
      case Message.Snapshot:{const mid=r.u32();const mn=r.u16();const payload=r.bytes();if(mid!==matchId)return;moveNumber=mn;handleSnapshot(payload);break}
      case Message.GameEnd:{const mid=r.u32();const text=r.str();if(mid===matchId)status(text||'対局終了');break}
      case Message.Disconnect:status(r.str()||'通信が終了しました');break;
      case Message.ConsensusRequest:{const id=r.u32(),action=r.u8(),requester=r.i32();const label=['','待った','リセット','タイトルへ','投了'][action]||'操作';if(confirm(`プレイヤー${requester+1}から「${label}」の確認です。賛成しますか？`))sendConsensusVote(id,true);else sendConsensusVote(id,false);break}
      case Message.ConsensusCommit:{r.u32();r.u8();r.bool();r.bytes();setTimeout(()=>sendSnapshotRequest(),100);break}
    }
  }catch(e){status(`受信エラー: ${e.message}`)}
}

function handleSnapshot(payload){
  if(payload.length>=4&&ascii(payload,0,4)==='QST1'){currentState=parseQuickState(payload);pointActions=null;selectedPointSlot=-1;renderState();return}
  if(payload.length>=4&&ascii(payload,0,4)==='QAC1'){pointActions=parseQuickActions(payload);renderState();return}
  status('Quick Join状態を待っています…');
}
function parseQuickState(bytes){
  const r=new Reader(bytes);r.raw(4);const format=r.u8(),boardSize=r.u8(),seat=r.i8(),currentDisc=r.u8(),playerCount=r.u8(),flags=r.u8(),moveNo=r.u16();const order=[];for(let i=0;i<4;i++)order.push(r.u8());const points=[];for(let i=0;i<4;i++)points.push(r.u16());const obstacles=[];for(let i=0;i<4;i++)obstacles.push(r.u8());const expansion=[];for(let i=0;i<4;i++)expansion.push(r.u8());const pointCosts=[],pointAbilities=[];for(let i=0;i<4;i++)pointCosts.push(r.u8());for(let i=0;i<4;i++)pointAbilities.push(r.u8());const clocks=[];for(let i=0;i<5;i++)clocks.push(r.i32());const cellCount=r.u16(),cells=[];for(let i=0;i<cellCount;i++)cells.push({row:r.u8(),col:r.u8(),disc:r.u8(),flags:r.u8(),reservation:r.u8()});const actionCount=r.u16(),actions=[];for(let i=0;i<actionCount;i++)actions.push(readAction(r));return {format,boardSize,seat,currentDisc,playerCount,flags,moveNo,order,points,obstacles,expansion,pointCosts,pointAbilities,clocks,cells,actions}
}
function parseQuickActions(bytes){const r=new Reader(bytes);r.raw(4);const format=r.u8(),slot=r.u8(),ability=r.u8(),mode=r.u8(),count=r.u16();if(mode===1){const sources=[];for(let i=0;i<count;i++)sources.push({row:r.u8(),col:r.u8()});return {format,slot,ability,mode,sources,actions:[]}}const actions=[];for(let i=0;i<count;i++)actions.push(readAction(r));return {format,slot,ability,mode,sources:[],actions}}
function readAction(r){return {kind:r.u8(),row:r.u8(),col:r.u8(),auxRow:decodeSigned(r.u8()),auxCol:decodeSigned(r.u8()),option:decodeSigned(r.u8())}}
function decodeSigned(v){return v===255?-1:v}

function showLobby(){
  $('connectCard').classList.add('hidden');$('lobbyCard').classList.remove('hidden');$('seatLabel').textContent=localSeat>=0?`プレイヤー${localSeat+1}`:'接続中';if(!rules)return;const humans=(rules.participantTypes||[]).slice(0,rules.participantCount).filter(x=>x===0).length;$('rules').textContent=`${ModeNames[rules.modeIndex]||'対戦'} / ${rules.participantCount}人（人間${humans}・AI${rules.participantCount-humans}） / ${rules.boardSize}×${rules.boardSize}${rules.totalTimeSeconds>0?` / ${Math.round(rules.totalTimeSeconds/60)}分`:''}`;const mask=1<<localSeat;ready=!!(lobby.readyMask&mask);$('readyButton').textContent=ready?'準備取消':'準備完了';$('readyButton').onclick=()=>{sendReady(!ready)}
}
function renderState(){
  const s=currentState;if(!s)return;moveNumber=s.moveNo;$('moveLabel').textContent=`${moveNumber}手`;$('turnLabel').textContent=s.flags&1?'対局終了':`${DiscNames[s.currentDisc]||''}の手番`;
  const myDisc=s.order[localSeat]||0;const p=myDisc?s.points[myDisc-1]:0;const ob=myDisc?s.obstacles[myDisc-1]:0;const ex=myDisc?s.expansion[myDisc-1]:0;$('resources').textContent=`あなた: ${DiscNames[myDisc]||`P${localSeat+1}`}　ポイント ${p}　障害物 ${ob}${s.flags&2?`　拡張 ${ex}`:''}`;
  renderPointBar(s,myDisc);renderBoard(s);status((s.flags&1)?'対局終了':(seatForDisc(s,s.currentDisc)===localSeat?'あなたの手番です':'相手の手番です'));
}
function renderPointBar(s,myDisc){const bar=$('pointBar');bar.innerHTML='';if(!(s.flags&16)||!myDisc)return;for(let slot=0;slot<4;slot++){const b=document.createElement('button');const ability=s.pointAbilities[slot];const cost=s.pointCosts[slot];b.textContent=`${AbilityNames[ability]||'特殊'} ${cost}P`;b.disabled=s.points[myDisc-1]<cost||seatForDisc(s,s.currentDisc)!==localSeat;b.classList.toggle('selected',selectedPointSlot===slot);b.onclick=()=>requestPointSlot(slot);bar.appendChild(b)}}
function requestPointSlot(slot,srcRow=-1,srcCol=-1){selectedPointSlot=slot;const bytes=new Uint8Array([81,80,65,49,slot,srcRow<0?255:srcRow,srcCol<0?255:srcCol]);sendSnapshotRequest(bytes);status('特殊操作を取得しています…')}
function renderBoard(s){
  const board=$('board');board.innerHTML='';const map=new Map(s.cells.map(c=>[`${c.row},${c.col}`,c]));let minR=0,maxR=s.boardSize-1,minC=0,maxC=s.boardSize-1;if(s.flags&2){const coords=s.cells.filter(c=>c.flags&4);if(coords.length){minR=Math.max(0,Math.min(...coords.map(c=>c.row))-1);maxR=Math.min(s.boardSize-1,Math.max(...coords.map(c=>c.row))+1);minC=Math.max(0,Math.min(...coords.map(c=>c.col))-1);maxC=Math.min(s.boardSize-1,Math.max(...coords.map(c=>c.col))+1)}}const cols=maxC-minC+1;board.style.gridTemplateColumns=`repeat(${cols},max-content)`;
  let activeActions=s.actions||[], sourceSet=new Set();if(pointActions){if(pointActions.mode===1)for(const q of pointActions.sources)sourceSet.add(`${q.row},${q.col}`);else activeActions=pointActions.actions}
  const legalMap=new Map();for(const a of activeActions){const k=`${a.row},${a.col}`;if(!legalMap.has(k))legalMap.set(k,[]);legalMap.get(k).push(a)}
  for(let r=minR;r<=maxR;r++)for(let c=minC;c<=maxC;c++){const key=`${r},${c}`,rec=map.get(key),cell=document.createElement('button');cell.className='cell';if((s.flags&2)&&(!rec||!(rec.flags&4)))cell.classList.add('inactive');if(legalMap.has(key))cell.classList.add('legal');if(sourceSet.has(key))cell.classList.add('source');if(rec){if(rec.disc){const d=document.createElement('span');d.className=`disc ${['','black','white','red','blue'][rec.disc]}`;cell.appendChild(d)}if(rec.flags&2){const o=document.createElement('span');o.className='obstacle';cell.appendChild(o)}if(rec.flags&1){const b=document.createElement('span');b.className='bomb';b.textContent='●';cell.appendChild(b)}if(rec.reservation){const rv=document.createElement('span');rv.className='reservation';cell.appendChild(rv)}}cell.onclick=()=>onCell(r,c,legalMap.get(key)||[],sourceSet.has(key));board.appendChild(cell)}
}
function onCell(row,col,actions,isSource){if(isSource&&pointActions&&pointActions.mode===1){requestPointSlot(pointActions.slot,row,col);return}if(!actions.length)return;if(actions.length===1){sendMove(actions[0]);pointActions=null;return}showActionSheet(actions)}
function showActionSheet(actions){const sh=$('actionSheet');sh.innerHTML='';sh.classList.remove('hidden');for(const a of actions){const b=document.createElement('button');b.textContent=moveLabel(a);b.onclick=()=>{sh.classList.add('hidden');sendMove(a)};sh.appendChild(b)}}
function moveLabel(a){if(a.kind===0)return'駒を置く';if(a.kind===1)return'障害物';const n={10:'敵駒消去',11:'二連続',12:'十字変換',13:'周囲変換',14:'障害物',15:'予約',16:'自駒移動',17:'リスク二連',18:'自由配置'};return n[a.kind]||`特殊 ${a.kind}`}
function seatForDisc(s,disc){return s.order.indexOf(disc)}

class WebBluetoothTransport {
  constructor(){this.device=null;this.server=null;this.rx=null;this.tx=null;this.writeQueue=Promise.resolve()}
  async connect(){
    if(!window.isSecureContext)throw new Error('ChromeのBluetooth参加にはHTTPSが必要です。QRを読み直してください。');
    if(!navigator.bluetooth)throw new Error('このChromeではWeb Bluetoothを利用できません。Android版Chromeを更新してください。');
    // requestDevice must be the first async permission operation after the button gesture.
    const device=await navigator.bluetooth.requestDevice({filters:[{services:[SERVICE]}]});
    this.device=device;
    const expected=`OTHELLO-${room}`;
    if(device.name&&device.name.startsWith('OTHELLO-')&&device.name!==expected){
      throw new Error(`合言葉が違うホストです。${expected} を選択してください。`);
    }
    device.addEventListener('gattserverdisconnected',()=>status('Bluetooth接続が切れました'));
    const server=await device.gatt.connect();
    this.server=server;
    const service=await server.getPrimaryService(SERVICE);
    this.rx=await service.getCharacteristic(RX);
    this.tx=await service.getCharacteristic(TX);
    await this.tx.startNotifications();
    this.tx.addEventListener('characteristicvaluechanged',e=>{
      const v=e.target.value;
      receiveFrame(new Uint8Array(v.buffer,v.byteOffset,v.byteLength));
    });
  }
  sendFrame(frame){
    if(!this.rx)return Promise.reject(new Error('Bluetoothホストと接続されていません'));
    const data=frame instanceof Uint8Array?frame:new Uint8Array(frame);
    this.writeQueue=this.writeQueue.catch(()=>{}).then(async()=>{
      if(typeof this.rx.writeValueWithResponse==='function')await this.rx.writeValueWithResponse(data);
      else await this.rx.writeValue(data);
    });
    return this.writeQueue;
  }
}
class NativeBleTransport {
  constructor(){this.pending=null;window.QuickJoinNativeEvent=e=>this.onEvent(typeof e==='string'?JSON.parse(e):e)}
  connect(){return new Promise((resolve,reject)=>{this.pending={resolve,reject};window.webkit.messageHandlers.quickJoinBLE.postMessage({action:'connect',room})})}
  sendFrame(frame){window.webkit.messageHandlers.quickJoinBLE.postMessage({action:'send',data:toBase64(frame)});return Promise.resolve()}
  onEvent(e){if(e.type==='connected'){this.pending?.resolve();this.pending=null}else if(e.type==='frame'){receiveFrame(fromBase64(e.data))}else if(e.type==='error'){this.pending?.reject(new Error(e.message||'Bluetoothエラー'));this.pending=null;status(e.message||'Bluetoothエラー')}else if(e.type==='disconnected')status('Bluetooth接続が切れました')}
}

const roomInput=$('roomInput'),roomInputWrap=$('roomInputWrap');
function syncRoomInput(){
  if(roomInput)roomInput.value=room;
  if(roomInputWrap)roomInputWrap.classList.toggle('hidden',!!room);
  $('room').textContent=`合言葉 ${room||'------'}`;
}
if(roomInput){roomInput.oninput=()=>{room=roomInput.value.replace(/\D/g,'').slice(0,6);roomInput.value=room;$('room').textContent=`合言葉 ${room||'------'}`}}
syncRoomInput();
$('connectButton').textContent=window.__QUICKJOIN_NATIVE__?'Bluetoothで参加':'ChromeでBluetooth参加';
$('connectButton').onclick=async()=>{
  if(!/^\d{6}$/.test(room)){if(roomInputWrap)roomInputWrap.classList.remove('hidden');roomInput?.focus();status('ホスト画面の6桁の合言葉を入力してください');return}
  try{$('connectButton').disabled=true;status(window.__QUICKJOIN_NATIVE__?'Bluetoothホストを探しています…':'ChromeのBluetooth一覧を開きます…');transport=window.__QUICKJOIN_NATIVE__?new NativeBleTransport():new WebBluetoothTransport();await transport.connect();status('ホストへ参加しています…');sendJoin()}catch(e){status(e.message||String(e));$('connectButton').disabled=false}
};
$('supportNote').textContent=window.__QUICKJOIN_NATIVE__?'QRの合言葉を使ってホストへBluetoothで直接接続します。':`ChromeのBluetooth一覧から OTHELLO-${room||'------'} を選択してください。Wi-Fiは不要です。`;

function ascii(b,o,n){return String.fromCharCode(...b.slice(o,o+n))}
function randomHex(n){const a=new Uint8Array(Math.ceil(n/2));crypto.getRandomValues(a);return [...a].map(x=>x.toString(16).padStart(2,'0')).join('').slice(0,n)}
function status(t){$('status').textContent=t}
function toBase64(a){let s='';for(const b of a)s+=String.fromCharCode(b);return btoa(s)}
function fromBase64(s){const b=atob(s),a=new Uint8Array(b.length);for(let i=0;i<b.length;i++)a[i]=b.charCodeAt(i);return a}
})();
