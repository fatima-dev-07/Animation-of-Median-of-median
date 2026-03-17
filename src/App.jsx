import { useState, useEffect, useRef, useCallback, useMemo } from "react";

const C = {
  bg: "#080c18", bgCard: "#0d1321", bgNode: "#111b2e",
  border: "#1e2d4a", borderLight: "#2a3f66",
  text: "#c9d6e8", textDim: "#5e7491", textBright: "#eaf0f9",
  cyan: "#00e5ff", cyanDim: "#00e5ff33",
  green: "#00e676", greenDim: "#00e67633",
  orange: "#ff9100", orangeDim: "#ff910033",
  pink: "#ff4081", pinkDim: "#ff408133",
  yellow: "#ffea00", yellowDim: "#ffea0033",
  purple: "#b388ff", purpleDim: "#b388ff33",
  white: "#fff",
};

const CALL_STYLES = {
  root: { main: C.orange, dim: C.orangeDim, label: "ROOT" },
  mom: { main: C.purple, dim: C.purpleDim, label: "MoM" },
  left: { main: C.cyan, dim: C.cyanDim, label: "LEFT" },
  right: { main: C.pink, dim: C.pinkDim, label: "RIGHT" },
};

const GRP_COLORS = ["#4dabf7", "#06d6a0", "#ff6b35", "#fbbf24", "#c084fc", "#f472b6", "#38bdf8", "#a3e635"];

/* ═══ Text/sizing helpers ═══ */
const CHAR_W = 7, MAX_LINE = 32, MIN_W = 150, MAX_W = 400, BASE_H = 82, GAP_X = 36, GAP_Y = 120;

function splitArr(seg) {
  const items = seg.map(String), lines = []; let cur = "";
  for (let i = 0; i < items.length; i++) {
    const sep = cur ? ", " : "";
    if ((cur + sep + items[i]).length > MAX_LINE && cur) { lines.push(cur + ","); cur = items[i]; }
    else cur = cur + sep + items[i];
  }
  if (cur) lines.push(cur);
  return lines;
}
function nodeW(seg) { return Math.max(MIN_W, Math.min(MAX_W, Math.min(seg.join(", ").length, MAX_LINE) * CHAR_W + 44)); }
function nodeH(seg) { return BASE_H + Math.max(0, splitArr(seg).length - 1) * 14; }

/* ═══════════════════════════════════════════
   ALGORITHM TRACER — with detailed sub-steps
   ═══════════════════════════════════════════ */
function traceExecution(inputArr, kInput) {
  let nid = 0;
  const nodes = new Map();
  const timeline = [];

  function addNode(pid, seg, left, right, k, type) {
    const id = nid++;
    const node = { id, parentId: pid, left, right, k, callType: type, segment: [...seg], children: [], result: null, pivot: null, medians: null, rank: null, _w: nodeW(seg), _h: nodeH(seg) };
    nodes.set(id, node);
    if (pid !== null && nodes.has(pid)) nodes.get(pid).children.push(id);
    return id;
  }

  function partition(arr, left, right, pivotValue) {
    let pivotIndex = left;
    for (let i = left; i <= right; i++) { if (arr[i] === pivotValue) { pivotIndex = i; break; } }
    [arr[pivotIndex], arr[right]] = [arr[right], arr[pivotIndex]];
    let storeIndex = left;
    for (let i = left; i < right; i++) {
      if (arr[i] < pivotValue) { [arr[i], arr[storeIndex]] = [arr[storeIndex], arr[i]]; storeIndex++; }
    }
    [arr[storeIndex], arr[right]] = [arr[right], arr[storeIndex]];
    return storeIndex;
  }

  function findMedian(arr, left, size) {
    const sub = arr.slice(left, left + size).sort((a, b) => a - b);
    for (let i = 0; i < size; i++) arr[left + i] = sub[i];
    return arr[left + Math.floor(size / 2)];
  }

  function solve(arr, left, right, k, parentId, callType) {
    const seg = arr.slice(left, right + 1);
    const nodeId = addNode(parentId, seg, left, right, k, callType);

    timeline.push({ t: "enter", id: nodeId, msg: `Enter [${left}..${right}], k=${k}`, detail: { type: "subarray", arr: [...seg], left, right, k } });

    if (left === right) {
      nodes.get(nodeId).result = arr[left];
      timeline.push({ t: "base", id: nodeId, msg: `Base → return ${arr[left]}`, detail: { type: "base", value: arr[left] } });
      return arr[left];
    }

    const n = right - left + 1;

    // Step 1: Form groups of 5
    const groupsBefore = [];
    for (let i = 0; i < Math.floor(n / 5); i++) {
      const gl = left + i * 5;
      groupsBefore.push({ start: gl, size: 5, elements: arr.slice(gl, gl + 5) });
    }
    if (n % 5 !== 0) {
      const gl = left + Math.floor(n / 5) * 5;
      groupsBefore.push({ start: gl, size: n % 5, elements: arr.slice(gl, right + 1) });
    }

    timeline.push({
      t: "divide", id: nodeId,
      msg: `Divide ${n} elements into ${groupsBefore.length} groups of ≤5`,
      detail: { type: "groups", groups: groupsBefore.map(g => ({ ...g, elements: [...g.elements] })), arr: arr.slice(left, right + 1), left, right }
    });

    // Step 2: Sort each group and find medians
    const medians = [];
    const groupsAfter = [];
    for (let i = 0; i < groupsBefore.length; i++) {
      const gl = groupsBefore[i].start;
      const sz = groupsBefore[i].size;
      const med = findMedian(arr, gl, sz);
      medians.push(med);
      groupsAfter.push({ start: gl, size: sz, sorted: arr.slice(gl, gl + sz), median: med });
    }

    nodes.get(nodeId).medians = [...medians];

    timeline.push({
      t: "medians", id: nodeId,
      msg: `Sort groups & pick medians: [${medians.join(", ")}]`,
      detail: { type: "medians", groupsAfter, medians: [...medians], arr: arr.slice(left, right + 1), left, right }
    });

    // Step 3: Find MoM
    let medOfMed;
    if (medians.length === 1) {
      medOfMed = medians[0];
      timeline.push({ t: "pivot_direct", id: nodeId, msg: `Single median → pivot = ${medOfMed}`, detail: { type: "pivot", pivot: medOfMed, medians: [...medians] } });
    } else {
      const mArr = [...medians];
      const mK = Math.floor(medians.length / 2);
      timeline.push({ t: "spawn_mom", id: nodeId, msg: `Recurse: find MoM of [${mArr.join(", ")}], k=${mK}`, detail: { type: "spawn_mom", mediansArr: [...mArr], mK } });
      medOfMed = solve(mArr, 0, mArr.length - 1, mK, nodeId, "mom");
      timeline.push({ t: "got_pivot", id: nodeId, msg: `MoM returned → pivot = ${medOfMed}`, detail: { type: "pivot", pivot: medOfMed, medians: [...medians] } });
    }
    nodes.get(nodeId).pivot = medOfMed;

    // Step 4: Partition — show before and after
    const arrBefore = arr.slice(left, right + 1);
    const pivotIndex = partition(arr, left, right, medOfMed);
    const rank = pivotIndex - left + 1;
    nodes.get(nodeId).rank = rank;
    const arrAfter = arr.slice(left, right + 1);

    // Build color map: less / pivot / greater
    const partColors = arrAfter.map((v, i) => {
      const absI = left + i;
      if (absI < pivotIndex) return "less";
      if (absI === pivotIndex) return "pivot";
      return "greater";
    });

    timeline.push({
      t: "partition", id: nodeId,
      msg: `Partition around pivot=${medOfMed} → index ${pivotIndex}, rank=${rank}`,
      detail: { type: "partition", pivot: medOfMed, pivotIndex, rank, arrBefore, arrAfter, partColors, left, right }
    });

    // Step 5: Recurse
    if (k === rank) {
      nodes.get(nodeId).result = arr[pivotIndex];
      timeline.push({ t: "found", id: nodeId, msg: `k=${k} == rank=${rank} → FOUND ${arr[pivotIndex]}`, detail: { type: "found", value: arr[pivotIndex] } });
      return arr[pivotIndex];
    } else if (k < rank) {
      timeline.push({ t: "go_left", id: nodeId, msg: `k=${k} < rank=${rank} → go LEFT [${left}..${pivotIndex - 1}]`, detail: { type: "recurse", direction: "left", newLeft: left, newRight: pivotIndex - 1, newK: k, arrAfter, partColors, pivotIndex, left, right } });
      const res = solve(arr, left, pivotIndex - 1, k, nodeId, "left");
      nodes.get(nodeId).result = res;
      timeline.push({ t: "returned", id: nodeId, msg: `Left returned → ${res}`, detail: { type: "return", value: res } });
      return res;
    } else {
      timeline.push({ t: "go_right", id: nodeId, msg: `k=${k} > rank=${rank} → go RIGHT [${pivotIndex + 1}..${right}], k=${k - rank}`, detail: { type: "recurse", direction: "right", newLeft: pivotIndex + 1, newRight: right, newK: k - rank, arrAfter, partColors, pivotIndex, left, right } });
      const res = solve(arr, pivotIndex + 1, right, k - rank, nodeId, "right");
      nodes.get(nodeId).result = res;
      timeline.push({ t: "returned", id: nodeId, msg: `Right returned → ${res}`, detail: { type: "return", value: res } });
      return res;
    }
  }

  const arr = [...inputArr];
  const result = solve(arr, 0, arr.length - 1, kInput, null, "root");
  timeline.push({ t: "done", id: 0, msg: `Answer: ${result}`, detail: { type: "done", value: result } });
  const sorted = [...inputArr].sort((a, b) => a - b);
  return { nodes, timeline, result, expected: sorted[kInput - 1] };
}

/* ═══ LAYOUT ═══ */
function layoutTree(nm) {
  if (nm.size === 0) return new Map();
  const pos = new Map();
  let rootId = null;
  for (const [id, n] of nm) { if (n.parentId === null) { rootId = id; break; } }
  if (rootId === null) return pos;
  function dep(id, d) { const n = nm.get(id); if (!n) return; n._d = d; n.children.forEach(c => dep(c, d + 1)); }
  dep(rootId, 0);
  const sw = new Map();
  function subW(id) { const n = nm.get(id); if (!n) return 0; if (!n.children.length) { sw.set(id, n._w); return n._w; } const cw = n.children.map(subW); const t = cw.reduce((a, b) => a + b, 0) + (n.children.length - 1) * GAP_X; const w = Math.max(n._w, t); sw.set(id, w); return w; }
  subW(rootId);
  function place(id, cx, y) { const n = nm.get(id); if (!n) return; pos.set(id, { x: cx, y, w: n._w, h: n._h }); if (!n.children.length) return; const cw = n.children.map(c => sw.get(c) || 0); const tot = cw.reduce((a, b) => a + b, 0) + (n.children.length - 1) * GAP_X; let lx = cx - tot / 2; for (let i = 0; i < n.children.length; i++) { place(n.children[i], lx + cw[i] / 2, y + n._h + GAP_Y); lx += cw[i] + GAP_X; } }
  place(rootId, 0, 0);
  return pos;
}

/* ═══ DETAIL PANEL — shows inside-node operations ═══ */
function DetailPanel({ detail, step }) {
  if (!detail) return <div style={{ padding: 16, color: C.textDim, fontSize: 11 }}>Step through to see details...</div>;

  const cellStyle = (bg, border, color) => ({
    display: "inline-flex", alignItems: "center", justifyContent: "center",
    width: 40, height: 40, borderRadius: 8, fontSize: 13, fontWeight: 700,
    fontFamily: "'JetBrains Mono',monospace",
    background: bg, border: `2px solid ${border}`, color,
    transition: "all 0.3s",
  });

  switch (detail.type) {
    case "subarray":
      return (
        <div style={{ padding: 16 }}>
          <Label>Working on subarray [{detail.left}..{detail.right}], finding k={detail.k}th smallest</Label>
          <div style={{ display: "flex", gap: 4, flexWrap: "wrap", marginTop: 10 }}>
            {detail.arr.map((v, i) => (
              <div key={i} style={{ display: "flex", flexDirection: "column", alignItems: "center", gap: 2 }}>
                <div style={cellStyle(C.bgNode, C.cyan, C.cyan)}>{v}</div>
                <span style={{ fontSize: 8, color: C.textDim }}>{detail.left + i}</span>
              </div>
            ))}
          </div>
        </div>
      );

    case "groups":
      return (
        <div style={{ padding: 16 }}>
          <Label>Step 1: Divide into groups of 5</Label>
          <div style={{ display: "flex", gap: 12, flexWrap: "wrap", marginTop: 10 }}>
            {detail.groups.map((g, gi) => {
              const gc = GRP_COLORS[gi % GRP_COLORS.length];
              return (
                <div key={gi} style={{ background: `${gc}11`, border: `1px solid ${gc}44`, borderRadius: 10, padding: "8px 12px" }}>
                  <div style={{ fontSize: 9, color: gc, fontWeight: 800, marginBottom: 6, fontFamily: "'JetBrains Mono',monospace" }}>Group {gi + 1} (idx {g.start}–{g.start + g.size - 1})</div>
                  <div style={{ display: "flex", gap: 4 }}>
                    {g.elements.map((v, vi) => (
                      <div key={vi} style={cellStyle(`${gc}15`, gc, gc)}>{v}</div>
                    ))}
                  </div>
                </div>
              );
            })}
          </div>
        </div>
      );

    case "medians":
      return (
        <div style={{ padding: 16 }}>
          <Label>Step 2: Sort each group & pick middle element (median)</Label>
          <div style={{ display: "flex", gap: 12, flexWrap: "wrap", marginTop: 10 }}>
            {detail.groupsAfter.map((g, gi) => {
              const gc = GRP_COLORS[gi % GRP_COLORS.length];
              const midIdx = Math.floor(g.size / 2);
              return (
                <div key={gi} style={{ background: `${gc}11`, border: `1px solid ${gc}44`, borderRadius: 10, padding: "8px 12px" }}>
                  <div style={{ fontSize: 9, color: gc, fontWeight: 800, marginBottom: 6, fontFamily: "'JetBrains Mono',monospace" }}>Group {gi + 1} (sorted)</div>
                  <div style={{ display: "flex", gap: 4 }}>
                    {g.sorted.map((v, vi) => (
                      <div key={vi} style={cellStyle(
                        vi === midIdx ? `${C.yellow}33` : `${gc}15`,
                        vi === midIdx ? C.yellow : gc,
                        vi === midIdx ? C.yellow : gc
                      )}>{v}</div>
                    ))}
                  </div>
                  {<div style={{ fontSize: 8, color: C.yellow, marginTop: 4, textAlign: "center", fontFamily: "'JetBrains Mono',monospace" }}>median = {g.median}</div>}
                </div>
              );
            })}
          </div>
          <div style={{ marginTop: 14, padding: "8px 14px", background: `${C.yellow}11`, border: `1px solid ${C.yellow}33`, borderRadius: 8 }}>
            <span style={{ fontSize: 10, color: C.yellow, fontWeight: 800, fontFamily: "'JetBrains Mono',monospace" }}>
              Medians collected → [{detail.medians.join(", ")}]
            </span>
          </div>
        </div>
      );

    case "pivot":
      return (
        <div style={{ padding: 16 }}>
          <Label>Pivot selected</Label>
          <div style={{ marginTop: 10, display: "inline-flex", alignItems: "center", gap: 10, padding: "12px 20px", background: `${C.orange}15`, border: `2px solid ${C.orange}`, borderRadius: 12 }}>
            <span style={{ fontSize: 10, color: C.textDim }}>pivot =</span>
            <span style={{ fontSize: 24, fontWeight: 900, color: C.orange, fontFamily: "'JetBrains Mono',monospace" }}>{detail.pivot}</span>
          </div>
          {detail.medians.length > 1 && (
            <div style={{ marginTop: 8, fontSize: 10, color: C.textDim }}>
              (Median of medians from [{detail.medians.join(", ")}])
            </div>
          )}
        </div>
      );

    case "spawn_mom":
      return (
        <div style={{ padding: 16 }}>
          <Label>Need to find median of medians — spawning recursive call</Label>
          <div style={{ display: "flex", gap: 4, flexWrap: "wrap", marginTop: 10 }}>
            {detail.mediansArr.map((v, i) => (
              <div key={i} style={cellStyle(`${C.purple}22`, C.purple, C.purple)}>{v}</div>
            ))}
          </div>
          <div style={{ marginTop: 8, fontSize: 10, color: C.purple, fontFamily: "'JetBrains Mono',monospace" }}>
            → Recurse to find k={detail.mK}th smallest of these {detail.mediansArr.length} medians
          </div>
        </div>
      );

    case "partition":
      return (
        <div style={{ padding: 16 }}>
          <Label>Step 3: Partition around pivot = {detail.pivot}</Label>
          <div style={{ marginTop: 6, fontSize: 10, color: C.textDim, marginBottom: 4 }}>Before partition:</div>
          <div style={{ display: "flex", gap: 4, flexWrap: "wrap" }}>
            {detail.arrBefore.map((v, i) => (
              <div key={i} style={{ display: "flex", flexDirection: "column", alignItems: "center", gap: 2 }}>
                <div style={cellStyle(
                  v === detail.pivot ? `${C.orange}33` : C.bgNode,
                  v === detail.pivot ? C.orange : C.border,
                  v === detail.pivot ? C.orange : C.text
                )}>{v}</div>
                <span style={{ fontSize: 8, color: C.textDim }}>{detail.left + i}</span>
              </div>
            ))}
          </div>

          <div style={{ marginTop: 14, fontSize: 10, color: C.textDim, marginBottom: 4 }}>After partition:</div>
          <div style={{ display: "flex", gap: 4, flexWrap: "wrap" }}>
            {detail.arrAfter.map((v, i) => {
              const pc = detail.partColors[i];
              const bg = pc === "less" ? `${C.green}22` : pc === "pivot" ? `${C.orange}33` : `${C.pink}22`;
              const br = pc === "less" ? C.green : pc === "pivot" ? C.orange : C.pink;
              const co = pc === "less" ? C.green : pc === "pivot" ? C.orange : C.pink;
              return (
                <div key={i} style={{ display: "flex", flexDirection: "column", alignItems: "center", gap: 2 }}>
                  <div style={cellStyle(bg, br, co)}>{v}</div>
                  <span style={{ fontSize: 8, color: C.textDim }}>{detail.left + i}</span>
                </div>
              );
            })}
          </div>

          <div style={{ display: "flex", gap: 14, marginTop: 10, fontSize: 10, fontFamily: "'JetBrains Mono',monospace" }}>
            <span style={{ color: C.green }}>■ &lt; pivot ({detail.pivot})</span>
            <span style={{ color: C.orange }}>■ PIVOT at idx {detail.pivotIndex}</span>
            <span style={{ color: C.pink }}>■ &gt; pivot</span>
            <span style={{ color: C.textDim, marginLeft: 8 }}>rank = {detail.rank}</span>
          </div>
        </div>
      );

    case "recurse":
      return (
        <div style={{ padding: 16 }}>
          <Label>Step 4: Recurse {detail.direction.toUpperCase()} side</Label>
          <div style={{ display: "flex", gap: 4, flexWrap: "wrap", marginTop: 10 }}>
            {detail.arrAfter.map((v, i) => {
              const absI = detail.left + i;
              const inNew = absI >= detail.newLeft && absI <= detail.newRight;
              const isPivot = detail.partColors[i] === "pivot";
              const bg = isPivot ? `${C.orange}33` : inNew ? (detail.direction === "left" ? `${C.cyan}22` : `${C.pink}22`) : `${C.textDim}11`;
              const br = isPivot ? C.orange : inNew ? (detail.direction === "left" ? C.cyan : C.pink) : `${C.textDim}33`;
              const co = isPivot ? C.orange : inNew ? (detail.direction === "left" ? C.cyan : C.pink) : `${C.textDim}55`;
              return (
                <div key={i} style={{ display: "flex", flexDirection: "column", alignItems: "center", gap: 2 }}>
                  <div style={cellStyle(bg, br, co)}>{v}</div>
                  <span style={{ fontSize: 8, color: inNew ? C.textBright : `${C.textDim}55` }}>{absI}</span>
                </div>
              );
            })}
          </div>
          <div style={{ marginTop: 8, fontSize: 10, color: detail.direction === "left" ? C.cyan : C.pink, fontFamily: "'JetBrains Mono',monospace" }}>
            → Recurse on [{detail.newLeft}..{detail.newRight}] with k={detail.newK}
          </div>
        </div>
      );

    case "found":
      return (
        <div style={{ padding: 16 }}>
          <Label>FOUND! k-th smallest element</Label>
          <div style={{ marginTop: 12, display: "inline-flex", alignItems: "center", gap: 10, padding: "16px 28px", background: `${C.yellow}15`, border: `3px solid ${C.yellow}`, borderRadius: 14, boxShadow: `0 0 30px ${C.yellowDim}` }}>
            <span style={{ fontSize: 32, fontWeight: 900, color: C.yellow, fontFamily: "'JetBrains Mono',monospace" }}>{detail.value}</span>
          </div>
        </div>
      );

    case "base":
      return (
        <div style={{ padding: 16 }}>
          <Label>Base case — single element</Label>
          <div style={{ marginTop: 10, display: "inline-flex" }}>
            <div style={cellStyle(`${C.green}22`, C.green, C.green)}>{detail.value}</div>
          </div>
        </div>
      );

    case "return":
      return (
        <div style={{ padding: 16 }}>
          <Label>Child returned value</Label>
          <div style={{ marginTop: 10, display: "inline-flex", alignItems: "center", gap: 8, padding: "10px 18px", background: `${C.green}11`, border: `2px solid ${C.green}`, borderRadius: 10 }}>
            <span style={{ fontSize: 10, color: C.textDim }}>result =</span>
            <span style={{ fontSize: 20, fontWeight: 900, color: C.green, fontFamily: "'JetBrains Mono',monospace" }}>{detail.value}</span>
          </div>
        </div>
      );

    case "done":
      return (
        <div style={{ padding: 16 }}>
          <Label>Final Answer</Label>
          <div style={{ marginTop: 12, display: "inline-flex", alignItems: "center", gap: 10, padding: "16px 28px", background: `${C.yellow}15`, border: `3px solid ${C.yellow}`, borderRadius: 14, boxShadow: `0 0 30px ${C.yellowDim}` }}>
            <span style={{ fontSize: 32, fontWeight: 900, color: C.yellow, fontFamily: "'JetBrains Mono',monospace" }}>{detail.value}</span>
          </div>
        </div>
      );

    default:
      return <div style={{ padding: 16, color: C.textDim, fontSize: 11 }}>{step?.msg || ""}</div>;
  }
}

function Label({ children }) {
  return <div style={{ fontSize: 11, fontWeight: 700, color: C.textBright, fontFamily: "'JetBrains Mono',monospace", marginBottom: 4 }}>{children}</div>;
}

/* ═══ SVG NODE ═══ */
function SNode({ node, pos, state, selected, onClick }) {
  if (!pos) return null;
  const { x, y, w, h } = pos;
  const cc = CALL_STYLES[node.callType] || CALL_STYLES.root;
  let border = C.border, bg = C.bgNode, op = 0.35, lc = C.textDim;
  const glow = state === "active" || state === "found";
  if (state === "active") { border = C.cyan; bg = "#0a1e36"; op = 1; lc = C.cyan; }
  else if (state === "work") { border = C.orange; bg = "#1e1508"; op = 1; lc = C.orange; }
  else if (state === "done") { border = C.green; bg = "#081e12"; op = 1; lc = C.green; }
  else if (state === "found") { border = C.yellow; bg = "#1e1c08"; op = 1; lc = C.yellow; }
  else if (state === "vis") { op = 0.6; border = C.borderLight; }

  const lines = splitArr(node.segment);
  const bw = cc.label.length * 7.5 + 14;

  return (
    <g onClick={onClick} style={{ cursor: "pointer" }}>
      {glow && <rect x={x - w / 2 - 5} y={y - 5} width={w + 10} height={h + 10} rx={14} fill="none" stroke={border} strokeWidth={2} opacity={0.35}><animate attributeName="opacity" values="0.2;0.5;0.2" dur="1.5s" repeatCount="indefinite" /></rect>}
      <rect x={x - w / 2} y={y} width={w} height={h} rx={12} fill={bg} stroke={border} strokeWidth={selected ? 3 : 1.5} opacity={op} />
      <clipPath id={`c${node.id}`}><rect x={x - w / 2 + 2} y={y + 1} width={w - 4} height={h - 2} rx={11} /></clipPath>
      <g clipPath={`url(#c${node.id})`} opacity={op}>
        <rect x={x - w / 2 + 8} y={y + 6} width={bw} height={15} rx={4} fill={cc.dim} />
        <text x={x - w / 2 + 15} y={y + 16.5} fontSize={8} fontWeight={800} fill={cc.main} fontFamily="'JetBrains Mono',monospace" style={{ letterSpacing: 1 }}>{cc.label}</text>
        {lines.map((l, i) => <text key={i} x={x} y={y + 30 + i * 14} textAnchor="middle" fontSize={10.5} fontWeight={700} fill={lc} fontFamily="'JetBrains Mono',monospace">{i === 0 ? "[" : " "}{l}{i === lines.length - 1 ? "]" : ""}</text>)}
        <text x={x} y={y + 30 + lines.length * 14 + 2} textAnchor="middle" fontSize={9.5} fill={C.textDim} fontFamily="'JetBrains Mono',monospace">k={node.k}{node.pivot !== null ? ` pivot=${node.pivot}` : ""}</text>
      </g>
      {node.result !== null && (state === "done" || state === "found") && <g><rect x={x + w / 2 - 34} y={y + 4} width={28} height={17} rx={5} fill={state === "found" ? C.yellow : C.green} opacity={0.9} /><text x={x + w / 2 - 20} y={y + 15.5} textAnchor="middle" fontSize={9.5} fontWeight={900} fill={C.bg} fontFamily="'JetBrains Mono',monospace">{node.result}</text></g>}
    </g>
  );
}

/* ═══ SVG EDGE ═══ */
function SEdge({ parent, child, childNode, active, returning, positions }) {
  const pp = positions.get(parent), cp = positions.get(child);
  if (!pp || !cp) return null;
  const x1 = pp.x, y1 = pp.y + pp.h, x2 = cp.x, y2 = cp.y, my = (y1 + y2) / 2;
  const path = `M ${x1} ${y1} C ${x1} ${my}, ${x2} ${my}, ${x2} ${y2}`;
  const rev = `M ${x2} ${y2} C ${x2} ${my}, ${x1} ${my}, ${x1} ${y1}`;
  const cc = CALL_STYLES[childNode.callType] || CALL_STYLES.root;
  const ec = active ? C.cyan : returning ? C.green : cc.main;
  const eo = active || returning ? 1 : 0.5;
  const ew = active || returning ? 3 : 2;
  const mx = (x1 + x2) / 2, ly = my - 6;
  return (
    <g>
      <path d={path} fill="none" stroke={ec} strokeWidth={ew + 3} opacity={0.08} />
      <path d={path} fill="none" stroke={ec} strokeWidth={ew} opacity={eo} strokeDasharray={active ? "8 4" : "none"}>{active && <animate attributeName="stroke-dashoffset" from="24" to="0" dur="0.7s" repeatCount="indefinite" />}</path>
      <polygon points={`${x2},${y2} ${x2 - 5},${y2 - 9} ${x2 + 5},${y2 - 9}`} fill={ec} opacity={eo} />
      <rect x={mx - cc.label.length * 3.5 - 5} y={ly - 7} width={cc.label.length * 7 + 10} height={14} rx={3} fill={C.bg} stroke={cc.main} strokeWidth={1} opacity={0.85} />
      <text x={mx} y={ly + 3} textAnchor="middle" fontSize={7.5} fontWeight={800} fill={cc.main} fontFamily="'JetBrains Mono',monospace" opacity={0.9}>{cc.label}</text>
      {(active || returning) && <circle r={4} fill={active ? C.cyan : C.green} opacity={0.9}><animateMotion dur="0.9s" repeatCount="indefinite" path={returning ? rev : path} /></circle>}
    </g>
  );
}

/* ═══ MAIN APP ═══ */
export default function App() {
  const [input, setInput] = useState("12, 3, 5, 7, 4, 19, 26, 1, 9, 15");
  const [kVal, setKVal] = useState(8);
  const [data, setData] = useState(null);
  const [step, setStep] = useState(0);
  const [play, setPlay] = useState(false);
  const [speed, setSpeed] = useState(1000);
  const [sel, setSel] = useState(null);
  const [zoom, setZoom] = useState(1);
  const [pan, setPan] = useState({ x: 0, y: 0 });
  const [cW, setCW] = useState(800);
  const cRef = useRef(null);
  const dragR = useRef(null);
  const intR = useRef(null);

  useEffect(() => { const el = cRef.current; if (!el) return; const ob = new ResizeObserver(e => { for (const en of e) setCW(en.contentRect.width); }); ob.observe(el); setCW(el.clientWidth); return () => ob.disconnect(); }, []);

  const run = useCallback(() => {
    const arr = input.split(",").map(s => parseInt(s.trim())).filter(n => !isNaN(n));
    if (!arr.length) return;
    const k = Math.max(1, Math.min(kVal, arr.length));
    setData(traceExecution(arr, k)); setStep(0); setPlay(false); setSel(null); setZoom(1); setPan({ x: 0, y: 0 });
  }, [input, kVal]);

  useEffect(() => {
    if (play && data) { intR.current = setInterval(() => { setStep(p => { if (p >= data.timeline.length - 1) { setPlay(false); return p; } return p + 1; }); }, speed); }
    return () => clearInterval(intR.current);
  }, [play, speed, data]);

  const positions = useMemo(() => data ? layoutTree(data.nodes) : new Map(), [data]);

  const { nStates, vis, aEdges, msg } = useMemo(() => {
    if (!data) return { nStates: new Map(), vis: new Set(), aEdges: new Map(), msg: "" };
    const st = new Map(), v = new Set(), ae = new Map(); let m = "", an = null;
    for (let i = 0; i <= step && i < data.timeline.length; i++) {
      const s = data.timeline[i]; m = s.msg;
      if (an !== null && st.get(an) === "active") st.set(an, "vis");
      switch (s.t) {
        case "enter": v.add(s.id); st.set(s.id, "active"); an = s.id; ae.clear(); { const nd = data.nodes.get(s.id); if (nd?.parentId !== null) ae.set(s.id, "down"); } break;
        case "divide": case "medians": case "partition": case "spawn_mom": case "go_left": case "go_right": case "pivot_direct":
          st.set(s.id, "work"); an = s.id; ae.clear(); break;
        case "got_pivot": case "returned":
          st.set(s.id, "active"); an = s.id; ae.clear();
          { const nd = data.nodes.get(s.id); if (nd) { for (let ci = nd.children.length - 1; ci >= 0; ci--) { if (v.has(nd.children[ci])) { ae.set(nd.children[ci], "up"); break; } } } }
          break;
        case "base": st.set(s.id, "done"); an = s.id; ae.clear(); break;
        case "found": st.set(s.id, "found"); an = s.id; ae.clear(); break;
        case "done": ae.clear(); for (const [id] of data.nodes) { if (v.has(id) && st.get(id) !== "found") st.set(id, "done"); } break;
      }
    }
    return { nStates: st, vis: v, aEdges: ae, msg: m };
  }, [data, step]);

  const mD = (e) => { if (e.button === 0) dragR.current = { sx: e.clientX - pan.x, sy: e.clientY - pan.y }; };
  const mM = (e) => { if (dragR.current) setPan({ x: e.clientX - dragR.current.sx, y: e.clientY - dragR.current.sy }); };
  const mU = () => { dragR.current = null; };
  const wh = useCallback((e) => { e.preventDefault(); setZoom(z => Math.max(0.15, Math.min(3, z - e.deltaY * 0.001))); }, []);
  useEffect(() => { const el = cRef.current; if (el) el.addEventListener("wheel", wh, { passive: false }); return () => { if (el) el.removeEventListener("wheel", wh); }; }, [wh]);

  const cur = data?.timeline[step];

  return (
    <div style={{ height: "100vh", background: C.bg, color: C.text, fontFamily: "'IBM Plex Mono','Fira Code',monospace", display: "flex", flexDirection: "column", overflow: "hidden" }}>

      {/* HEADER */}
      <div style={{ padding: "8px 16px", borderBottom: `1px solid ${C.border}`, background: C.bgCard, display: "flex", alignItems: "center", gap: 8, flexWrap: "wrap", flexShrink: 0 }}>
        <div style={{ width: 26, height: 26, borderRadius: 6, background: `linear-gradient(135deg, ${C.cyan}, ${C.purple})`, display: "flex", alignItems: "center", justifyContent: "center", fontSize: 13, fontWeight: 900, color: C.bg }}>M</div>
        <span style={{ fontSize: 12, fontWeight: 800, color: C.textBright }}>Median of Medians</span>
        <span style={{ fontSize: 8, color: C.textDim }}>RECURSION TREE</span>
        <div style={{ display: "flex", gap: 5, alignItems: "center", marginLeft: "auto", flexWrap: "wrap" }}>
          <input value={input} onChange={e => setInput(e.target.value)} style={{ padding: "4px 8px", width: 190, background: C.bg, border: `1px solid ${C.border}`, borderRadius: 5, color: C.text, fontSize: 10, fontFamily: "inherit", outline: "none" }} />
          <span style={{ fontSize: 9, color: C.textDim }}>k=</span>
          <input type="number" min={1} value={kVal} onChange={e => setKVal(parseInt(e.target.value) || 1)} style={{ padding: "4px", width: 34, background: C.bg, border: `1px solid ${C.border}`, borderRadius: 5, color: C.text, fontSize: 10, fontFamily: "inherit", outline: "none", textAlign: "center" }} />
          <button onClick={run} style={{ padding: "4px 14px", background: `linear-gradient(135deg, ${C.cyan}, ${C.purple})`, border: "none", borderRadius: 5, color: C.bg, fontSize: 9, fontWeight: 800, cursor: "pointer", fontFamily: "inherit" }}>RUN</button>
          {[{ l: "n=5", a: "3, 1, 5, 2, 4", k: 3 }, { l: "n=10", a: "12, 3, 5, 7, 4, 19, 26, 1, 9, 15", k: 8 }, { l: "Lecture", a: "3,2,5,26,11,12,47,25,56,7,34,22,15,9,1,98,45,30,28,19,10,33,70,50,60", k: 13 }].map((p, i) => (
            <button key={i} onClick={() => { setInput(p.a); setKVal(p.k); }} style={{ padding: "2px 6px", background: "transparent", border: `1px solid ${C.border}`, borderRadius: 3, color: C.textDim, fontSize: 8, cursor: "pointer", fontFamily: "inherit" }}
              onMouseOver={e => { e.target.style.borderColor = C.cyan; e.target.style.color = C.cyan; }}
              onMouseOut={e => { e.target.style.borderColor = C.border; e.target.style.color = C.textDim; }}>{p.l}</button>
          ))}
        </div>
      </div>

      {/* CONTROLS */}
      {data && (
        <div style={{ padding: "6px 16px", borderBottom: `1px solid ${C.border}`, display: "flex", gap: 4, alignItems: "center", background: C.bgCard, flexWrap: "wrap", flexShrink: 0 }}>
          <B onClick={() => { setStep(0); setPlay(false); }}>⏮</B>
          <B onClick={() => setStep(Math.max(0, step - 1))}>◀</B>
          <B hl onClick={() => setPlay(!play)}>{play ? "⏸" : "▶"}</B>
          <B onClick={() => setStep(Math.min(data.timeline.length - 1, step + 1))}>▶</B>
          <B onClick={() => { setStep(data.timeline.length - 1); setPlay(false); }}>⏭</B>
          <div style={{ flex: 1, minWidth: 50, height: 4, background: C.bg, borderRadius: 2, cursor: "pointer" }}
            onClick={e => { const r = e.currentTarget.getBoundingClientRect(); setStep(Math.round(((e.clientX - r.left) / r.width) * (data.timeline.length - 1))); }}>
            <div style={{ width: `${((step + 1) / data.timeline.length) * 100}%`, height: "100%", borderRadius: 2, background: `linear-gradient(90deg, ${C.cyan}, ${C.purple})`, transition: "width 0.15s" }} />
          </div>
          <span style={{ fontSize: 9, color: C.textDim }}>{step + 1}/{data.timeline.length}</span>
          {[{ l: "½×", v: 1800 }, { l: "1×", v: 1000 }, { l: "2×", v: 500 }, { l: "4×", v: 250 }].map(s => (
            <button key={s.l} onClick={() => setSpeed(s.v)} style={{ padding: "1px 4px", fontSize: 8, background: speed === s.v ? `${C.cyan}22` : "transparent", border: `1px solid ${speed === s.v ? C.cyan : C.border}`, borderRadius: 3, color: speed === s.v ? C.cyan : C.textDim, cursor: "pointer", fontFamily: "inherit" }}>{s.l}</button>
          ))}
          <span style={{ fontSize: 8, color: C.textDim, marginLeft: 4 }}>Zoom</span>
          <B onClick={() => setZoom(z => Math.max(0.15, z - 0.15))}>−</B>
          <span style={{ fontSize: 8, color: C.textDim, minWidth: 24, textAlign: "center" }}>{Math.round(zoom * 100)}%</span>
          <B onClick={() => setZoom(z => Math.min(2.5, z + 0.15))}>+</B>
          <B onClick={() => { setZoom(1); setPan({ x: 0, y: 0 }); }}>⌂</B>
          {data.result === data.expected
            ? <span style={{ fontSize: 9, color: C.green, marginLeft: 8 }}>✓ Answer: {data.result}</span>
            : <span style={{ fontSize: 9, color: C.pink, marginLeft: 8 }}>✗ {data.result} ≠ {data.expected}</span>}
        </div>
      )}

      {/* MAIN AREA */}
      <div style={{ flex: 1, display: "flex", flexDirection: "column", overflow: "hidden" }}>
        {/* TREE */}
        <div ref={cRef}
          style={{ flex: 1, overflow: "hidden", position: "relative", background: `radial-gradient(ellipse at center, ${C.bgCard} 0%, ${C.bg} 70%)`, minHeight: 200 }}
          onMouseDown={mD} onMouseMove={mM} onMouseUp={mU} onMouseLeave={mU}>
          {data ? (
            <svg width="100%" height="100%" style={{ display: "block", cursor: dragR.current ? "grabbing" : "grab" }}>
              <defs><pattern id="g" width="40" height="40" patternUnits="userSpaceOnUse"><path d="M 40 0 L 0 0 0 40" fill="none" stroke={C.border} strokeWidth="0.3" opacity="0.2" /></pattern></defs>
              <rect width="100%" height="100%" fill="url(#g)" />
              <g transform={`translate(${pan.x + cW / 2}, ${pan.y + 30}) scale(${zoom})`}>
                {Array.from(data.nodes.values()).map(nd => {
                  if (nd.parentId === null || !vis.has(nd.id) || !vis.has(nd.parentId)) return null;
                  return <SEdge key={`e${nd.id}`} parent={nd.parentId} child={nd.id} childNode={nd} active={aEdges.get(nd.id) === "down"} returning={aEdges.get(nd.id) === "up"} positions={positions} />;
                })}
                {Array.from(data.nodes.values()).map(nd => {
                  if (!vis.has(nd.id)) return null;
                  return <SNode key={`n${nd.id}`} node={nd} pos={positions.get(nd.id)} state={nStates.get(nd.id) || "vis"} selected={sel === nd.id} onClick={() => setSel(nd.id === sel ? null : nd.id)} />;
                })}
              </g>
            </svg>
          ) : (
            <div style={{ display: "flex", flexDirection: "column", alignItems: "center", justifyContent: "center", height: "100%", padding: 24, textAlign: "center" }}>
              <div style={{ fontSize: 36, marginBottom: 12 }}>🌳</div>
              <h2 style={{ fontSize: 16, fontWeight: 800, color: C.textBright, margin: "0 0 6px" }}>Recursion Tree Visualizer</h2>
              <p style={{ fontSize: 10, color: C.textDim, maxWidth: 340, lineHeight: 1.6, margin: 0 }}>Enter array + k, click <b style={{ color: C.cyan }}>RUN</b>. See groups, medians, partitions, and recursion step by step.</p>
            </div>
          )}
        </div>

        {/* DETAIL PANEL — bottom */}
        {data && (
          <div style={{ borderTop: `2px solid ${C.border}`, background: C.bgCard, flexShrink: 0, maxHeight: "40vh", overflowY: "auto" }}>
            {/* Step message bar */}
            <div style={{ padding: "6px 16px", borderBottom: cur?.t === "done" ? "none" : `1px solid ${C.border}`, display: "flex", alignItems: "center", gap: 8, background: C.bg }}>
              {cur && <SB step={cur} msg={msg} />}
            </div>
            {/* Detailed visualization */}
            <DetailPanel detail={cur?.detail} step={cur} />
          </div>
        )}
      </div>
    </div>
  );
}

function B({ children, onClick, hl }) {
  return <button onClick={onClick} style={{ width: 22, height: 20, display: "flex", alignItems: "center", justifyContent: "center", background: hl ? `${C.cyan}22` : "transparent", border: `1px solid ${hl ? C.cyan : C.border}`, borderRadius: 3, color: hl ? C.cyan : C.text, fontSize: 10, cursor: "pointer", fontFamily: "inherit" }}>{children}</button>;
}
function SB({ step, msg }) {
  const tc = { enter: C.cyan, base: C.green, divide: C.purple, medians: C.yellow, partition: C.pink, spawn_mom: C.purple, go_left: C.cyan, go_right: C.pink, got_pivot: C.green, returned: C.green, pivot_direct: C.orange, found: C.yellow, done: C.yellow };
  const co = tc[step.t] || C.textDim;
  return <div><span style={{ display: "inline-block", padding: "1px 5px", borderRadius: 3, background: `${co}22`, color: co, fontSize: 8, fontWeight: 800, letterSpacing: 1, textTransform: "uppercase", marginRight: 6 }}>{step.t.replace(/_/g, " ")}</span><span style={{ fontSize: 10, color: C.text }}>{msg}</span></div>;
}
