-- Prove2me | solution 1 for DetDLP.M3A.FpPolyDefs.fpEntry_ordinary_vertex
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T09:36:25.527005+00:00
-- url     : https://prove2.me/submissions/f91d4217-d8dd-4104-944e-c4921765d510

import Definitions.Def_DetDLP_M3A_FpPolyDefs
import Definitions.Def_DetDLP_W3_IncQueryBounds

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace DetDLP.S8H0.GateAgree
open w4_M5Network
private theorem split_range (n m : ℕ) : List.finRange (n+m) =
    (List.finRange n).map (Fin.castAdd m) ++ (List.finRange m).map (Fin.natAdd n) := by
  simp only [← List.ofFn_id, List.map_ofFn]
  exact List.ofFn_add

private theorem disjoint_parts {n m : ℕ} (a : Fin m) (b : Fin n) :
    Fin.natAdd n a ≠ Fin.castAdd m b := by
  intro h; have he := congrArg Fin.val h; simp only [Fin.val_natAdd, Fin.val_castAdd] at he; omega

def gateEdges (A : w3_FactorLayout) (g : Fin A.ng) :=
  (List.finRange A.ne).filter (fun e => decide (A.gate e = g))

/-- Subdivision preserves ascending incidence order at an original factor gate. -/
theorem gate_ports (A : w3_FactorLayout) (g : Fin A.ng) :
    let G := w3_factorGraph A
    G.subdivision.ports (G.oldVertex (Fin.castAdd A.nb g)) =
      (gateEdges A g).map G.leftHalf := by
  let G := w3_factorGraph A
  let v := Fin.castAdd A.nb g
  let test := fun e : Fin (A.ne+A.ne) => decide
    ((G.subdivision.endpoints e).1 = G.oldVertex v ∨ (G.subdivision.endpoints e).2 = G.oldVertex v)
  change (List.finRange (A.ne+A.ne)).filter test = _
  rw [split_range, List.filter_append, List.filter_map, List.filter_map]
  have hl (e : Fin A.ne) : (test ∘ Fin.castAdd A.ne) e = decide (A.gate e = g) := by
    simp only [Function.comp_apply,test,G,v,w3_factorGraph,WireGraph.subdivision,WireGraph.oldVertex,
      Fin.addCases_left,Fin.castAdd_inj,disjoint_parts,or_false]
  have hr (e : Fin A.ne) : (test ∘ Fin.natAdd A.ne) e = false := by
    simp only [Function.comp_apply,test,G,v,w3_factorGraph,WireGraph.subdivision,WireGraph.oldVertex,
      Fin.addCases_right,Fin.castAdd_inj,disjoint_parts,or_false,decide_false]
  have hnil : (List.finRange A.ne).filter (test ∘ Fin.natAdd A.ne) = [] :=
    List.filter_eq_nil_iff.mpr (fun x _ => by rw [hr]; decide)
  rw [List.filter_congr (fun x _ => hl x), hnil, List.map_nil, List.append_nil]; rfl

private theorem idx_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (x : α) (l : List α) : (l.map f).idxOf (f x) = l.idxOf x := by
  induction l with
  | nil => rfl
  | cons h t ih => by_cases hh : h = x <;> simp_all [hf.eq_iff, eq_comm]

/-- At factor gates the abstract port index is exactly its rank among matching edges. -/
theorem gate_index (A : w3_FactorLayout) (g : Fin A.ng) (e : Fin A.ne) (h : A.gate e = g) :
    let G := w3_factorGraph A; let v := Fin.castAdd A.nb g
    (G.oldPort v (G.portIndex v e (w3_gateInc A g e h))).val = (gateEdges A g).idxOf e := by
  let G := w3_factorGraph A; let v := Fin.castAdd A.nb g
  change (G.subdivision.ports (G.oldVertex v)).idxOf (G.incidentHalf v
    ((G.ports v).get (G.portIndex v e _))) = _
  rw [G.get_portIndex v e (w3_gateInc A g e h),gate_ports A g]
  have hh : (G.endpoints e).1 = v := congrArg (Fin.castAdd A.nb) h
  have hi : G.incidentHalf v e = G.leftHalf e := if_pos hh
  rw [hi]
  exact idx_map _ (fun _ _ he => Fin.castAdd_inj.mp he) _ _

/-- Evaluate a factor gate using its local ports in increasing incidence order. -/
def localCheck (A : w3_FactorLayout) (t : w3_factorTest A) (g : Fin A.ng) (a : List Bool) :=
  t g fun e => a.getD ((gateEdges A g).idxOf e.val) false

theorem local_eq (A : w3_FactorLayout) (t : w3_factorTest A) (g : Fin A.ng) (a) :
    let G := w3_factorGraph A; let v := G.oldVertex (Fin.castAdd A.nb g)
    localCheck A t g (List.ofFn a) = G.subdivisionTensor (w3_factorChecks A t) v a := by
  dsimp only; rw [(w3_factorGraph A).subdivisionTensor_oldVertex (w3_factorChecks A t) (Fin.castAdd A.nb g) a]; simp only [w3_factorChecks, Fin.addCases_left,localCheck]
  congr 1; funext e; rw [← gate_index A g e.val e.property]
  simp [List.getD_eq_getElem?_getD]



theorem mul_gateEdges (G : WireGraph) (g : Fin G.nV) : gateEdges (w3_m5Layout G) g =
    ((List.finRange G.nE).filter (fun e => decide ((G.endpoints e).1 = g))).map G.leftHalf ++
    ((List.finRange G.nE).filter (fun e => decide ((G.endpoints e).2 = g))).map G.rightHalf := by
  change (List.finRange (G.nE+G.nE)).filter (fun e => decide (w3_m5HalfGate G e = g)) = _
  rw [split_range, List.filter_append, List.filter_map, List.filter_map]
  simp only [Function.comp_def, w3_m5HalfGate, Fin.addCases_left, Fin.addCases_right]
  rfl

end DetDLP.S8H0.GateAgree

namespace DetDLP.S8H0.PortEval
open w4_M5GraphBounds w4_M5PortTensor w4_M5Dispatch in
private theorem mul_tensor (q : List Unit) (hd : 1 ≤ q.length) (v : Fin (vertexCount q.length)) (a) :
    evalNat q v.val (List.ofFn a) = tensor hd v a := by
  let u := (vertexIndex q.length).symm v
  have hi : vertexIndex q.length u = v := (vertexIndex q.length).apply_symm_apply v
  have h := evalNat_at q hd u (List.ofFn a)
  rw [hi] at h
  exact h.trans ((w4_M5GateEq.gate_eq q hd v (List.ofFn a) u).trans (by
    unfold tensor; congr 2; funext i; simp [i.isLt]))

/-- The multiplication evaluator consumes the original W4 port order.  In particular
    a raw incidence assignment is pulled back along `w3_m5LocalInc` before dispatch. -/
theorem mul_eq {d : ℕ} (hd : 1 ≤ d) (v : Fin (w3_fpMulLayout d hd).ng) (a) :
    S8J.HashGatePoly.mulLayoutCheck d v.val
      (List.ofFn fun j => a (w3_m5LocalInc (w3_forgetSides (w4_M5GraphBounds.graph d hd)) v j)) =
      w3_fpMulTests d hd v a := by
  generalize hq : List.replicate d () = q
  have hw : q.length = d := by simp [←hq]
  subst d
  unfold S8J.HashGatePoly.mulLayoutCheck
  rw [hq]; exact mul_tensor q hd v _

end DetDLP.S8H0.PortEval

namespace DetDLP.S8H0.CoreCheck
open w4_M5GateOps
def reorder (q : Pad) (g : ℕ) (a : List Bool) :=
  let ps := portList q g
  let ls := ps.filter (fun e => decide (w4_M5EdgeNat.srcNat q.length e = g))
  let rs := ps.filter (fun e => decide (w4_M5EdgeNat.srcNat q.length e ≠ g))
  ps.map fun e => a.getD ((ls++rs).idxOf e) false

end DetDLP.S8H0.CoreCheck

namespace DetDLP.S8H0.LocalGateEq
open GateAgree
private theorem split_range (m n : ℕ) : List.finRange (m+n) =
    (List.finRange m).map (Fin.castAdd n) ++ (List.finRange n).map (Fin.natAdd m) := by
  simp only [← List.ofFn_id, List.map_ofFn]; exact List.ofFn_add
private theorem disj {m n : ℕ} (i : Fin m) (j : Fin n) : Fin.castAdd n i ≠ Fin.natAdd m j := by
  intro h; have H := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd] at H; omega
private theorem rank {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (l : List α) (i : α) : (l.map f).idxOf (f i) = l.idxOf i := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : x = i <;> simp_all [hf.eq_iff, eq_comm]
section Join
variable (A C : w3_FactorLayout) (s : w3_factorTest A) (t : w3_factorTest C)
private theorem left_edges (g : Fin A.ng) : gateEdges (S8J.join A C) (Fin.castAdd C.ng g) =
    (gateEdges A g).map (Fin.castAdd C.ne) := by
  simp only [gateEdges,S8J.join]
  rw [split_range,List.filter_append,List.filter_map,List.filter_map]
  simp [Function.comp_def,S8J.splitMap]; exact fun _ => (disj _ _).symm
private theorem right_edges (g : Fin C.ng) : gateEdges (S8J.join A C) (Fin.natAdd A.ng g) =
    (gateEdges C g).map (Fin.natAdd A.ne) := by
  simp only [gateEdges,S8J.join]
  rw [split_range,List.filter_append,List.filter_map,List.filter_map]
  simp [Function.comp_def,S8J.splitMap, disj]
theorem join_left (g : Fin A.ng) (bits : List Bool) :
    localCheck (S8J.join A C) (S8J.joinTest s t) (Fin.castAdd C.ng g) bits = localCheck A s g bits := by
  simp only [localCheck,S8J.joinTest,Fin.addCases_left,left_edges]
  congr 1; funext e; exact congrArg (fun i => bits.getD i false) (rank _ (fun _ _ h => Fin.castAdd_inj.mp h) _ _)
theorem join_right (g : Fin C.ng) (bits : List Bool) :
    localCheck (S8J.join A C) (S8J.joinTest s t) (Fin.natAdd A.ng g) bits = localCheck C t g bits := by
  simp only [localCheck,S8J.joinTest,Fin.addCases_right,right_edges]
  congr 1; funext e; exact congrArg (fun i => bits.getD i false) (rank _ (fun _ _ h => (Fin.natAdd_inj _).mp h) _ _)
end Join
def halves (G : w4_M5Network.WireGraph) (g : Fin G.nV) :=
  ((List.finRange G.nE).filter (fun i => decide ((G.endpoints i).1 = g))).map G.leftHalf ++
  ((List.finRange G.nE).filter (fun i => decide ((G.endpoints i).2 = g))).map G.rightHalf

open w4_M5GateOps w4_M5GraphBounds w4_M5EdgeNat w4_M5Network in
theorem reorder_eq (q : Pad) (hd : 1 ≤ q.length) (g : Fin (graph q.length hd).nV) (bits : List Bool) :
    let G := w3_forgetSides (graph q.length hd)
    CoreCheck.reorder q g bits = List.ofFn fun j => bits.getD ((halves G g).idxOf (w3_m5LocalInc G g j).val) false := by
  let D := graph q.length hd; let G := w3_forgetSides D
  change Fin G.nV at g
  have hs (e : Fin G.nE) : srcNat q.length e = (G.endpoints e).1.val := congrArg Prod.fst (endpointsNat_eq hd e)
  have ht (e : Fin G.nE) : dstNat q.length e = (G.endpoints e).2.val := congrArg Prod.snd (endpointsNat_eq hd e)
  have hp : portList q g = (G.ports g).map Fin.val := by
    unfold portList cap; erw [min_eq_left (show D.nE ≤ _ from (graph_edge_bound hd).le)]
    exact w4_M5PortEval.portsNat_eq D g _ _ hs ht
  let L := (List.finRange G.nE).filter fun i => decide ((G.endpoints i).1 = g)
  let R := (List.finRange G.nE).filter fun i => decide ((G.endpoints i).2 = g)
  have hl : (portList q g).filter (fun i => decide (srcNat q.length i = g)) = L.map Fin.val := by
    rw [hp,List.filter_map]; congr 1; unfold WireGraph.ports L; rw [List.filter_filter]; apply List.filter_congr
    intro e _; simp [hs,Fin.val_inj]; exact Or.inl
  have hr : (portList q g).filter (fun i => decide (srcNat q.length i ≠ g)) = R.map Fin.val := by
    rw [hp,List.filter_map]; congr 1; unfold WireGraph.ports R; rw [List.filter_filter]; apply List.filter_congr
    intro e _; by_cases h : (G.endpoints e).1 = g
    · have h' : (G.endpoints e).2 ≠ g := fun hh => G.loopless e (h.trans hh.symm)
      simp [hs,h,h']
    · simp [hs,Fin.val_inj,h]
  have HH : halves G g = (L++R).map (G.incidentHalf g) := by
    change L.map G.leftHalf ++ R.map G.rightHalf = _; rw [List.map_append]; apply congrArg₂ List.append
    · apply List.map_congr_left; intro e he; have h : (G.endpoints e).1 = g := by simpa [L] using he
      exact (if_pos h).symm
    · apply List.map_congr_left; intro e he; have h : (G.endpoints e).2 = g := by simpa [R] using he
      exact (if_neg (fun hh => G.loopless e (hh.trans h.symm))).symm
  change CoreCheck.reorder q g.val bits = List.ofFn fun j => bits.getD ((halves G g).idxOf (w3_m5LocalInc G g j).val) false
  simp only [CoreCheck.reorder,hl,hr,←List.map_append]; rw [hp,List.map_map]
  change _ = List.ofFn ((fun e => bits.getD ((halves G g).idxOf (G.incidentHalf g e)) false) ∘ (G.ports g).get)
  rw [←List.map_ofFn,List.ofFn_get,HH]; apply List.map_congr_left; intro e _
  simp only [Function.comp_apply,rank _ Fin.val_injective,rank _ (G.incidentHalf_injective g)]

end DetDLP.S8H0.LocalGateEq
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.M3A.OrdModels
open FpPolyDefs
open S8J S8H.PointAddresses S8L.FpPair.Address S8G.FpMoment S8L.FpPair S8L.FpPair.Stage.Links w4_M5PortTensor S8C FpSlotTile
attribute [-simp] Fin.natAdd_eq_addNat
variable {D M K : ℕ} (hd : 1 ≤ D)
theorem spl {a : Code} {A : w3_FactorLayout} {n : ℕ} {l r : Fin n → Fin A.nb} {L R : ℕ → ℕ} (ha : Models a A)
    (hl : ∀ u, L u.val = (l u).val) (hr : ∀ u, R u.val=(r u).val) : Models (splice a n L R) (links A l r) := by
  refine ⟨congrArg (·+n) ha.ng,ha.nb,congrArg (·+(n+n)) ha.ne,?_,?_⟩
  all_goals intro e;induction e using Fin.addCases with
    | left u => simp [splice,links,splitMap,ha.ne,u.isLt,ha.gate,ha.bit]
    | right u => induction u using Fin.addCases with
      | left u => simp [splice,links,splitMap,ha.ne,ha.ng,u.isLt,hl]
      | right u => simp [splice,links,splitMap,ha.ne,ha.ng,hr]
theorem out_val (i : Fin (2*D)) : w4_M5EdgeNat.edgeBase D 9 i.val = (ext hd (outPos i)).val := by unfold ext;rw [ext_outPos];rfl
theorem input_val (b : Bool) (i : Fin D) : (ext hd (inPos b i)).val = (if b then D+i.val else i.val) := by unfold ext;rw [ext_inPos];cases b <;> change _ + D*_ = _ <;> simp [tag,Nat.add_comm]
theorem addr_val (i : Fin (2*D)) (l : Fin 4) : addrN D i.val l.val=(addr hd i l).val := by simp only [addrN,(mul_spec hd).nb,addr,Fin.val_natAdd,AddLayout.reg];change _ = (_+_)+(4*i.val+l.val);ring
theorem linked_model : Models (linked D) (Stage.Links.layout hd) := by
  unfold linked;rw [show 4*D=2*D+2*D by omega]; apply spl (stage_spec hd)
  · intro e;induction e using Fin.addCases with
    | left u => simpa [left,u.isLt] using addr_val hd u 0
    | right u => simpa [left] using addr_val hd u 2
  · intro e;induction e using Fin.addCases with
    | left u => simp only [right,Fin.addCases_left,Fin.val_castAdd,if_pos u.isLt];rw [out_val hd,(mul_spec hd).nb];rfl
    | right u => simp [right,out_val hd];rfl
theorem stage_model : Models (stage D) (FpArithNet.boundedStage hd) := by
  apply spl (sum_spec (linked_model hd) (add_spec _))
  · intro i; simp only [(linked_model hd).nb,FpArithNet.stageOut,Fin.val_natAdd,AddLayout.reg,Fin.val_castSucc,Fin.val_zero,Nat.add_zero]
  · intro i;exact addr_val hd ⟨i.val,by omega⟩ 1

theorem chain_gate_count : (chains M D K).ng = (FpArithNet.chains hd M K).ng := by
  let A := FpSlotTile.slotLayout D K hd
  let B := FpArithNet.boundedStage hd
  change (4*M*(slot D K).ng+(2*M*(FpPolyDefs.stage D).ng+2*M*(FpPolyDefs.stage D).ng))+2*(4*M*D) =
    (4*M*A.ng+(2*M*B.ng+2*M*B.ng))+(4*M*D+4*M*D)
  have hA : (slot D K).ng=A.ng := (FpSlotTile.slot_models hd).ng
  have hB : (FpPolyDefs.stage D).ng=B.ng := (stage_model hd).ng
  rw [hA,hB]
  omega

theorem whole_gate_count (pre : List Bool) :
    (whole M D K pre.length).ng = (FpArithNet.layout hd M K pre).ng := by
  let n := min pre.length (4*M*D)
  change (chains M D K).ng+(n+1)+n+4*M=(FpArithNet.chains hd M K).ng+(n+1)+n+4*M
  rw [chain_gate_count hd]

end DetDLP.M3A.OrdModels
end

section
set_option autoImplicit false

namespace DetDLP.M3A.OrdPorts

open S8J S8G.FpMoment S8H0.GateAgree S8H.PointAddresses FpPolyDefs
attribute [-simp] Fin.natAdd_eq_addNat

theorem index_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (l : List α) (x : α) :
    (l.map f).idxOf (f x) = l.idxOf x := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : a = x <;> simp_all [hf.eq_iff, eq_comm]

theorem fin_disj {m n : ℕ} (i : Fin m) (j : Fin n) : Fin.castAdd n i ≠ Fin.natAdd m j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

private theorem split_range (m n : ℕ) :
    List.finRange (m+n) = (List.finRange m).map (Fin.castAdd n) ++
      (List.finRange n).map (Fin.natAdd m) := by
  simp only [← List.ofFn_id, List.map_ofFn]
  exact List.ofFn_add

theorem firstFiber {m n p q : ℕ} (f : Fin m → Fin p) (h : Fin n → Fin q) (i : Fin p) :
    (List.finRange (m+n)).filter (fun e => decide (splitMap f h e = Fin.castAdd q i)) =
      ((List.finRange m).filter (fun e => decide (f e = i))).map (Fin.castAdd n) := by
  rw [split_range, List.filter_append, List.filter_map, List.filter_map]
  simp [Function.comp_def, splitMap]
  exact fun j => (fin_disj _ _).symm

theorem lookup_old (A : w3_FactorLayout) {n k : ℕ} (bus : Fin n → Fin k → Fin A.nb)
    (t : w3_factorTest A) (g : Fin A.ng) (bits : List Bool) :
    localCheck (M3B.ECLayout.layout A bus) (M3B.ECLayout.test A bus t)
        (Fin.castAdd n g) bits = localCheck A t g bits := by
  have hp : gateEdges (M3B.ECLayout.layout A bus) (Fin.castAdd n g) =
      (gateEdges A g).map (Fin.castAdd (n*k)) := firstFiber _ _ _
  simp only [localCheck, M3B.ECLayout.test, Fin.addCases_left, hp]
  congr 1
  funext e
  exact congrArg (fun i => bits.getD i false)
    (index_map _ (fun _ _ h => Fin.castAdd_inj.mp h) _ _)

theorem links_old (A : w3_FactorLayout) {n : ℕ} (left right : Fin n → Fin A.nb)
    (t : w3_factorTest A) (g : Fin A.ng) (bits : List Bool) :
    localCheck (links A left right) (linksTest left right t) (Fin.castAdd n g) bits =
      localCheck A t g bits := by
  have hp : gateEdges (links A left right) (Fin.castAdd n g) =
      (gateEdges A g).map (Fin.castAdd (n+n)) := firstFiber _ _ _
  simp only [localCheck, linksTest, Fin.addCases_left, hp]
  congr 1
  funext e
  exact congrArg (fun i => bits.getD i false)
    (index_map _ (fun _ _ h => Fin.castAdd_inj.mp h) _ _)

theorem links_new_edges (A : w3_FactorLayout) {n : ℕ} (left right : Fin n → Fin A.nb) (g : Fin n) :
    gateEdges (links A left right) (Fin.natAdd A.ng g) =
      [Fin.natAdd A.ne (Fin.castAdd n g), Fin.natAdd A.ne (Fin.natAdd n g)] := by
  let l := Fin.natAdd A.ne (Fin.castAdd n g)
  let r := Fin.natAdd A.ne (Fin.natAdd n g)
  have hlr : l < r := by change A.ne + g.val < A.ne + (n + g.val); omega
  change (List.finRange (A.ne+(n+n))).filter
    (fun e => decide (splitMap A.gate (Fin.addCases id id) e = Fin.natAdd A.ng g)) = [l,r]
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
    ((List.pairwise_lt_finRange _).filter _) (by simp [hlr])
  intro e
  simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
    List.mem_cons, List.not_mem_nil, or_false]
  induction e using Fin.addCases with
  | left e =>
    simp [splitMap, l, r, fin_disj]
  | right e =>
    have hr' {a b : ℕ} (i : Fin a) (j : Fin b) : Fin.natAdd a j ≠ Fin.castAdd b i :=
      (fin_disj i j).symm
    induction e using Fin.addCases <;> simp [splitMap, l, r, fin_disj, hr']

theorem links_new (A : w3_FactorLayout) {n : ℕ} (left right : Fin n → Fin A.nb)
    (t : w3_factorTest A) (g : Fin n) (bits : List Bool) :
    localCheck (links A left right) (linksTest left right t) (Fin.natAdd A.ng g) bits =
      decide (bits.getD 0 false = bits.getD 1 false) := by
  let l := Fin.natAdd A.ne (Fin.castAdd n g)
  let r := Fin.natAdd A.ne (Fin.natAdd n g)
  have hlr : l < r := by change A.ne + g.val < A.ne + (n + g.val); omega
  have hp := links_new_edges A left right g
  simp only [localCheck, linksTest, Fin.addCases_right, hp]
  change decide (bits.getD ([l,r].idxOf l) false = bits.getD ([l,r].idxOf r) false) = _
  simp [ne_of_lt hlr]

theorem tile_edges {m : ℕ} (A : w3_FactorLayout) (i : Fin m) (g : Fin A.ng) :
    gateEdges (tiles m A) (finProdFinEquiv (i,g)) =
      (gateEdges A g).map (fun e => finProdFinEquiv (i,e)) := by
  have inc : StrictMono (fun e : Fin A.ne => finProdFinEquiv (i,e)) := by
    intro a b hab
    change a.val + A.ne*i.val < b.val + A.ne*i.val
    omega
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·)) ((List.pairwise_lt_finRange _).filter _)
    (((List.pairwise_lt_finRange _).filter _).map _ (fun _ _ h => inc h))
  intro e
  obtain ⟨⟨j,e⟩,rfl⟩ := finProdFinEquiv.surjective e
  simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
    tiles, tileMap_at, Equiv.apply_eq_iff_eq, Prod.mk.injEq, List.mem_map]
  exact ⟨fun ⟨h,h'⟩ => ⟨e,h',h.symm,rfl⟩,
    fun ⟨y,h,hy,hy'⟩ => ⟨hy.symm,hy' ▸ h⟩⟩

theorem tile_local {m : ℕ} (A : w3_FactorLayout) (ts : Fin m → w3_factorTest A)
    (i : Fin m) (g : Fin A.ng) (bits : List Bool) :
    localCheck (tiles m A) (tileTests ts) (finProdFinEquiv (i,g)) bits =
      localCheck A (ts i) g bits := by
  let f (u : Fin m × Fin A.ng) := ts u.1 u.2 (fun e =>
    bits.getD ((gateEdges (tiles m A) (finProdFinEquiv (i,g))).idxOf
      (finProdFinEquiv (u.1,e.val))) false)
  change f (finProdFinEquiv.symm (finProdFinEquiv (i,g))) = _
  rw [finProdFinEquiv.symm_apply_apply]
  dsimp only [f,localCheck]
  rw [tile_edges]
  congr 1
  funext e
  exact congrArg (fun k => bits.getD k false)
    (index_map _ (fun a b h => (Prod.mk.inj (finProdFinEquiv.injective h)).2) _ _)

theorem local_ports {c : Code} {A : w3_FactorLayout} (h : Models c A)
    (g : Fin A.ng) (bits : List Bool) :
    localPorts c g.val bits = ((gateEdges A g).map (fun e => (A.bit e).val)).zip bits := by
  unfold localPorts
  rw [h.ne, show List.range A.ne = (List.finRange A.ne).map Fin.val by simp, List.filter_map, List.map_map]
  have he : ((List.finRange A.ne).filter ((fun e => c.gate e == g.val) ∘ Fin.val)) = gateEdges A g := by
    unfold gateEdges
    apply List.filter_congr
    intro i _
    apply Bool.eq_iff_iff.mpr
    simp [h.gate, Fin.ext_iff]
  rw [he]
  congr 1
  apply List.map_congr_left
  intro e _
  exact h.bit e

end DetDLP.M3A.OrdPorts
end

section
set_option autoImplicit false

namespace DetDLP.M3A.OrdPorts

open S8J S8H0.GateAgree S8H.PointAddresses FpPolyDefs S8L.FpPair.Stage.Links

def addresses (A : w3_FactorLayout) (g : Fin A.ng) (bits : List Bool) :=
  ((gateEdges A g).map (fun e => (A.bit e).val)).zip bits

theorem pin_spec (A : w3_FactorLayout) (g : Fin A.ng) (bits : List Bool)
    (hlen : bits.length = (gateEdges A g).length) (k : ℕ) (index : ℕ → ℕ) (v : ℕ → Bool) :
    pin k (addresses A g bits) index v = true ↔
      ∀ (e : {e : Fin A.ne // A.gate e = g}) (i : Fin k),
        (A.bit e.val).val = index i.val → bits.getD ((gateEdges A g).idxOf e.val) false = v i.val := by
  let es := gateEdges A g
  have hm (e : Fin A.ne) : e ∈ es ↔ A.gate e = g := by simp [es,gateEdges]
  have hn : es.Nodup := (List.nodup_finRange _).filter _
  have hzip : addresses A g bits = List.ofFn (fun j : Fin es.length =>
      ((A.bit es[j.val]).val, bits.getD j.val false)) := by
    apply List.ext_getElem (by simp [addresses,hlen,es])
    intro i h₁ h₂
    have hi : i < bits.length := by simpa [hlen,es] using h₂
    simp [addresses,List.getElem_zip,List.getElem?_eq_getElem hi,es]
  rw [hzip]
  simp only [pin,List.all_eq_true,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,
    List.mem_range,decide_eq_true_eq]
  constructor
  · intro h e i he
    have hlt := List.idxOf_lt_length_of_mem ((hm e.val).mpr e.property)
    specialize h ⟨es.idxOf e.val,hlt⟩ i.val i.isLt
    simpa only [List.getElem_idxOf hlt] using h (by simpa only [List.getElem_idxOf hlt] using he)
  · intro h j i hi he
    have hg := (hm _).mp (List.getElem_mem j.isLt)
    exact (hn.idxOf_getElem j.val j.isLt) ▸ h ⟨_,hg⟩ ⟨i,hi⟩ he

theorem local_pins (A : w3_FactorLayout) {k : ℕ} (t : w3_factorTest A)
    (index : Fin k → Fin A.nb) (v : Fin k → Bool) (ixN : ℕ → ℕ) (vN : ℕ → Bool)
    (hi : ∀ i : Fin k, (index i).val = ixN i.val) (hv : ∀ i : Fin k, v i = vN i.val)
    (g : Fin A.ng) (bits : List Bool) (hlen : bits.length = (gateEdges A g).length) :
    localCheck A (atPins t index v) g bits = (localCheck A t g bits && pin k (addresses A g bits) ixN vN) := by
  classical
  unfold localCheck atPins
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq,pin_spec A g bits hlen]
  simp only [Fin.ext_iff,hi,hv]

end DetDLP.M3A.OrdPorts
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP.M3A.OrdPorts

open S8J S8H0.GateAgree FpPolyDefs
attribute [-simp] Fin.natAdd_eq_addNat

theorem join_left_edges (A B : w3_FactorLayout) (g : Fin A.ng) :
    gateEdges (join A B) (Fin.castAdd B.ng g) = (gateEdges A g).map (Fin.castAdd B.ne) :=
  firstFiber _ _ _

theorem join_right_edges (A B : w3_FactorLayout) (g : Fin B.ng) :
    gateEdges (join A B) (Fin.natAdd A.ng g) = (gateEdges B g).map (Fin.natAdd A.ne) := by
  have hs (m n : ℕ) : List.finRange (m+n) = (List.finRange m).map (Fin.castAdd n) ++
      (List.finRange n).map (Fin.natAdd m) := by
    simp only [← List.ofFn_id, List.map_ofFn]
    exact List.ofFn_add
  simp only [gateEdges,join]
  rw [hs,List.filter_append,List.filter_map,List.filter_map]
  simp [Function.comp_def,splitMap,fin_disj]

theorem links_old_edges (A : w3_FactorLayout) {n : ℕ} (l r : Fin n → Fin A.nb) (g : Fin A.ng) :
    gateEdges (links A l r) (Fin.castAdd n g) = (gateEdges A g).map (Fin.castAdd (n+n)) :=
  firstFiber _ _ _

theorem join_left_addresses (A B : w3_FactorLayout) (g : Fin A.ng) (bits : List Bool) :
    addresses (join A B) (Fin.castAdd B.ng g) bits = addresses A g bits := by
  unfold addresses
  erw [join_left_edges,List.map_map]
  simp [join,splitMap,Function.comp_def]

theorem links_old_addresses (A : w3_FactorLayout) {n : ℕ} (l r : Fin n → Fin A.nb)
    (g : Fin A.ng) (bits : List Bool) :
    addresses (links A l r) (Fin.castAdd n g) bits = addresses A g bits := by
  unfold addresses
  erw [links_old_edges,List.map_map]
  simp [links,Function.comp_def]

theorem links_equal (A : w3_FactorLayout) {n : ℕ} (l r : Fin n → Fin A.nb)
    (t : w3_factorTest A) (g : Fin n) (bits : List Bool)
    (hlen : bits.length = (gateEdges (links A l r) (Fin.natAdd A.ng g)).length) :
    equal bits = localCheck (links A l r) (linksTest l r t) (Fin.natAdd A.ng g) bits := by
  rw [links_new_edges] at hlen
  rw [links_new]
  obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hlen
  cases a <;> cases b <;> decide

end DetDLP.M3A.OrdPorts
end

section
set_option autoImplicit false

namespace DetDLP.M3A.OrdPorts

open S8C S8H0 S8H0.GateAgree FpPolyDefs

theorem add_edges {n : ℕ} (g : Fin n) : gateEdges (AddLayout.layout n) g =
    (List.finRange 5).map (AddLayout.pos g) := by
  have hf : StrictMono (AddLayout.pos g) := by
    intro a b hab
    change 5*g.val+a.val < 5*g.val+b.val
    omega
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·)) ((List.pairwise_lt_finRange _).filter _)
    ((List.pairwise_lt_finRange _).map _ fun _ _ h => hf h)
  intro e
  change (e ∈ (List.finRange (n*5)).filter (fun e => decide (AddLayout.col e = g))) ↔ _
  simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq,List.mem_map]
  constructor
  · intro h
    refine ⟨⟨e.val%5,by omega⟩,?_⟩
    have he := congrArg Fin.val h
    change e.val/5 = g.val at he
    apply Fin.ext
    change 5*g.val+e.val%5=e.val
    omega
  · rintro ⟨j,rfl⟩
    exact AddLayout.col_pos _ _

theorem add_rank {n : ℕ} (g : Fin n) (j : Fin 5) :
    (gateEdges (AddLayout.layout n) g).idxOf (AddLayout.pos g j) = j.val := by
  rw [add_edges,index_map]
  · exact List.idxOf_finRange _
  · intro a b h
    apply Fin.ext
    have := congrArg Fin.val h
    change 5*g.val+a.val = 5*g.val+b.val at this
    omega

theorem column_local {n : ℕ} (g : Fin n) (cin : Bool) (bits : List Bool) :
    col n g.val cin bits = localCheck (AddLayout.layout n) (AddLayout.test cin) g bits := by
  let f (get : Fin 5 → Bool) := decide ((get 0).toNat+(get 1).toNat+
    (if g.val=0 then cin else get 4).toNat=(get 2).toNat+2*(get 3).toNat ∧ (g.val+1=n → get 3=false))
  change f (fun j => bits.getD j.val false) =
    f (fun j => bits.getD ((gateEdges (AddLayout.layout n) g).idxOf (AddLayout.pos g j)) false)
  exact congrArg f (funext fun j : Fin 5 => congrArg (fun i => bits.getD i false) (add_rank g j).symm)

theorem strip_local {d : ℕ} (p T : ℕ) (g : Fin (8*(d+1))) (bits : List Bool) :
    rows d p T g.val bits =
      localCheck (AddLayout.layout (8*(d+1))) (S8G.FpPhysicalAtom.rowTest d p (min T p)) g bits := by
  let i := g.val%(d+1)
  let j := g.val/(d+1)
  let f (get : Fin 5 → Bool) := if j = 7 then
    decide (get 0 = get 3 ∧ get 2 = false ∧ (i ≠ 0 → get 0 = get 4) ∧ get 1 = (get 0 && p.testBit i))
    else decide ((get 0).toNat+(get 1).toNat+(if i=0 then decide (j<5) else get 4).toNat =
      (get 2).toNat+2*(get 3).toNat ∧ (i=d → get 3=false) ∧ (j<2 → get 1=false ∧ (i=d → get 2=false)) ∧
      (j=0 ∧ i=d → get 0=false) ∧ (j=2 ∨ j=4 → get 2=p.testBit i) ∧ (j=3 → get 2=(min T p).testBit i) ∧
      (j=5 ∧ i=d → get 0=false ∧ get 1=false))
  calc
    _ = f (fun l => bits.getD l.val false) := by
      by_cases h : g.val/(d+1)=7
      · simp only [rows,f,j,if_pos h]; rfl
      · simp only [rows,f,j,if_neg h]
        apply Bool.eq_iff_iff.mpr
        simp only [col,Bool.and_eq_true,decide_eq_true_eq,Nat.add_right_cancel_iff,and_assoc]
        rfl
    _ = f (fun l => bits.getD ((gateEdges (AddLayout.layout (8*(d+1))) g).idxOf (AddLayout.pos g l)) false) := by
      exact congrArg f (funext fun l : Fin 5 => congrArg (fun i => bits.getD i false) (add_rank g l).symm)
    _ = _ := rfl

private theorem mul_aux (q : w4_M5GateOps.Pad) (d : ℕ) (hlen : q.length = d) (hd : 1 ≤ d)
    (g : Fin (w3_fpMulLayout d hd).ng) (bits : List Bool) :
    S8J.HashGatePoly.mulLayoutCheck d g.val (CoreCheck.reorder q g.val bits) =
      localCheck (w3_fpMulLayout d hd) (w3_fpMulTests d hd) g bits := by
  subst d
  rw [LocalGateEq.reorder_eq q hd g bits]
  unfold localCheck
  rw [← PortEval.mul_eq]
  have he := mul_gateEdges (w3_forgetSides (w4_M5GraphBounds.graph q.length hd)) g
  change gateEdges (w3_fpMulLayout q.length hd) g = LocalGateEq.halves _ g at he
  rw [he]
  rfl

theorem multiply_local {d : ℕ} (hd : 1 ≤ d) (g : Fin (w3_fpMulLayout d hd).ng) (bits : List Bool) :
    mulCheck d g.val bits = localCheck (w3_fpMulLayout d hd) (w3_fpMulTests d hd) g bits := by
  rw [← mul_aux (List.replicate d ()) d (List.length_replicate ..)]
  simp only [mulCheck,CoreCheck.reorder,List.length_replicate,Bool.beq_eq_decide_eq,bne,decide_not]

end DetDLP.M3A.OrdPorts
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP.M3A.OrdPorts

open S8C S8H0.GateAgree S8L.FpPair.Stage.Links FpPolyDefs

theorem add_bit_lane {n : ℕ} (g : Fin n) (l : Fin 5) (i : Fin n) (k : Fin 4) (hk : k.val ≠ 3) :
    (AddLayout.layout n).bit (AddLayout.pos g l) = AddLayout.reg i k ↔ l.val = k.val ∧ g = i := by
  change AddLayout.bit (AddLayout.pos g l) = _ ↔ _
  rw [AddLayout.bit_pos]
  have hk' := k.isLt
  by_cases h : l.val < 4
  · simp only [dif_pos h,AddLayout.reg,Fin.ext_iff]
    omega
  · simp only [dif_neg h,AddLayout.reg,Fin.ext_iff]
    change 4*(AddLayout.prev g).val+3 = 4*i.val+k.val ↔ _
    omega

theorem column_pin_iff {n s : ℕ} (g : Fin n)
    (x : {e : Fin (n*5) // (AddLayout.layout n).gate e = g} → Bool)
    (k : Fin 4) (hk : k.val ≠ 3) (ix : Fin s → Fin n) (val : Fin s → Bool) :
    (∀ e i, (AddLayout.layout n).bit e.val = AddLayout.reg (ix i) k → x e = val i) ↔
      ∀ i, g = ix i →
        x ⟨AddLayout.pos g (Fin.castLE (by decide : 4 ≤ 5) k),AddLayout.col_pos ..⟩ = val i := by
  constructor
  · intro h i he
    exact h _ i ((add_bit_lane _ _ _ _ hk).mpr ⟨rfl,he⟩)
  · intro h e i he
    have hmem : e.val ∈ gateEdges (AddLayout.layout n) g := by simp [gateEdges,e.property]
    rw [add_edges] at hmem
    obtain ⟨l,_,hl⟩ := List.mem_map.mp hmem
    have hbits := (add_bit_lane _ _ _ _ hk).mp (hl ▸ he)
    specialize h i hbits.2
    have hpos : (Fin.castLE (by decide : 4 ≤ 5) k) = l := Fin.ext hbits.1.symm
    exact (congrArg x (Subtype.ext ((congrArg (AddLayout.pos g) hpos).trans hl))).symm.trans h

theorem range_local {d : ℕ} (p : ℕ) (g : Fin (d+1)) (bits : List Bool) :
    localCheck (AddLayout.layout (d+1))
      (atPins (atPins (AddLayout.test true) (fun j => AddLayout.reg j 2) (fun j => p.testBit j.val))
        (fun _ : Fin 1 => AddLayout.reg (Fin.last d) 0) (fun _ => false)) g bits =
      (col (d+1) g.val true bits && decide (bit bits 2=p.testBit g.val ∧ (g.val=d → bit bits 0=false))) := by
  classical
  let x (e : {e : Fin ((d+1)*5) // (AddLayout.layout (d+1)).gate e = g}) :=
    bits.getD ((gateEdges (AddLayout.layout (d+1)) g).idxOf e.val) false
  have hx (j : Fin 5) : x ⟨AddLayout.pos g j,AddLayout.col_pos ..⟩ = bit bits j.val :=
    congrArg (fun i => bits.getD i false) (add_rank g j)
  have hz := column_pin_iff g x (2 : Fin 4) (by decide) id (fun j => p.testBit j.val)
  have ha := column_pin_iff g x (0 : Fin 4) (by decide) (fun _ : Fin 1 => Fin.last d) (fun _ => false)
  rw [column_local]
  apply Bool.eq_iff_iff.mpr
  simp only [localCheck,atPins,Bool.and_eq_true,decide_eq_true_eq]
  change ((_ ∧ (∀ e i, (AddLayout.layout (d+1)).bit e.val = AddLayout.reg i 2 → x e=p.testBit i.val)) ∧
      (∀ e (_ : Fin 1), (AddLayout.layout (d+1)).bit e.val = AddLayout.reg (Fin.last d) 0 → x e=false)) ↔ _
  constructor
  · rintro ⟨⟨hc,hz'⟩,ha'⟩
    refine ⟨hc,(hx _).symm.trans (hz.mp hz' g rfl),?_⟩
    intro hg
    exact (hx _).symm.trans (ha.mp ha' 0 (Fin.ext hg))
  · rintro ⟨hc,hz',ha'⟩
    refine ⟨⟨hc,hz.mpr ?_⟩,ha.mpr ?_⟩
    · intro i hi
      exact (hx _).trans ((congrArg (fun j : Fin (d+1) => p.testBit j.val) hi) ▸ hz')
    · intro _ hi
      exact (hx _).trans (ha' (congrArg Fin.val hi))

end DetDLP.M3A.OrdPorts
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP.M3A.OrdPorts

open S8J S8C S8H0 S8H0.GateAgree S8L.FpPair S8L.FpPair.Stage.Links
open S8H.PointAddresses S8L.FpPair.Address FpPolyDefs w4_M5PortTensor
attribute [-simp] Fin.natAdd_eq_addNat

theorem linked_local {d : ℕ} (hd : 1 ≤ d) (g : Fin (Stage.Links.layout hd).ng) (bits : List Bool)
    (hlen : bits.length = (gateEdges (Stage.Links.layout hd) g).length) :
    linkedGate d g.val bits = localCheck (Stage.Links.layout hd) (linkedTests hd) g bits := by
  let M := (w3_fpMulLayout d hd).ng
  have hm : (mul d).ng = M := (mul_spec hd).ng
  have hs : (stageCode d).ng = M+M+2*d := rfl
  induction g using Fin.addCases with
  | left u =>
    erw [links_old]
    induction u using Fin.addCases with
    | left u =>
      erw [LocalGateEq.join_left]
      induction u using Fin.addCases with
      | left g =>
        erw [LocalGateEq.join_left]
        have hg : g.val < M := g.isLt
        simpa only [linkedGate,hm,Fin.val_castAdd,if_pos (show g.val < 2*M by omega),
          Nat.mod_eq_of_lt hg] using multiply_local hd g bits
      | right g =>
        erw [LocalGateEq.join_right]
        have hg : g.val < M := g.isLt
        change linkedGate d (M+g.val) bits = _
        rw [linkedGate,hm,if_pos (by omega),Nat.add_mod_left,Nat.mod_eq_of_lt hg]
        exact multiply_local hd g bits
    | right g =>
      erw [LocalGateEq.join_right]
      have hg : g.val < 2*d := g.isLt
      change linkedGate d (M+M+g.val) bits = _
      rw [linkedGate,hm,if_neg (by omega),hs,if_pos (by omega),
        show M+M+g.val-2*M=g.val by omega]
      exact column_local g false bits
  | right g =>
    change linkedGate d (M+M+2*d+g.val) bits = _
    rw [linkedGate,hm,if_neg (by omega),hs,if_neg (by omega)]
    exact links_equal _ _ _ _ _ _ hlen

theorem fixed_linked_local {d : ℕ} (hd : 1 ≤ d) (p : ℕ)
    (g : Fin (Stage.Links.layout hd).ng) (bits : List Bool)
    (hlen : bits.length = (gateEdges (Stage.Links.layout hd) g).length) :
    (linkedGate d g.val bits && stagePins d p (addresses (Stage.Links.layout hd) g bits)) =
      localCheck (Stage.Links.layout hd) (S8G.FpPhysicalAtom.stageTest hd p) g bits := by
  let ix (i : Fin d) := mul2 hd (inPos true i)
  let high (i : Fin d) := addr hd ⟨d+i.val,by omega⟩ 1
  have hx (i : Fin d) : (ix i).val = (mul d).nb+(d+i.val) := by
    change (w3_fpMulLayout d hd).nb+(ext hd (inPos true i)).val = _
    rw [OrdModels.input_val hd,(mul_spec hd).nb]
    rfl
  have hh (i : Fin d) : (high i).val = addrN d (d+i.val) 1 := (OrdModels.addr_val hd _ _).symm
  unfold S8G.FpPhysicalAtom.stageTest
  erw [local_pins (Stage.Links.layout hd) _ high (fun _ => false) (fun j => addrN d (d+j) 1) (fun _ => false)
      hh (fun _ => rfl) g bits hlen,
    local_pins (Stage.Links.layout hd) _ ix (fun i => p.testBit i.val) (fun j => (mul d).nb+(d+j)) p.testBit
      hx (fun _ => rfl) g bits hlen]
  rw [linked_local hd g bits hlen]
  exact Bool.and_assoc .. |>.symm

end DetDLP.M3A.OrdPorts
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP.M3A.OrdPorts

open S8J S8C S8H0 S8H0.GateAgree S8L.FpPair S8L.FpPair.Stage.Links
open S8H.PointAddresses S8L.FpPair.Address FpPolyDefs
attribute [-simp] Fin.natAdd_eq_addNat

def inner_stage (d p g : ℕ) (bits : List Bool) (ps : List (ℕ × Bool)) :=
  let L := (linked d).ng
  if g < L then linkedGate d g bits && stagePins d p ps else if g < L+d+1 then
    let i := g-L
    col (d+1) i true bits && decide (bit bits 2=p.testBit i ∧ (i=d → bit bits 0=false))
  else equal bits

theorem inner_stage_local {d : ℕ} (hd : 1 ≤ d) (p : ℕ) (g : Fin (FpArithNet.boundedStage hd).ng)
    (bits : List Bool) (hlen : bits.length = (gateEdges (FpArithNet.boundedStage hd) g).length) :
    inner_stage d p g.val bits (addresses (FpArithNet.boundedStage hd) g bits) =
      localCheck (FpArithNet.boundedStage hd) (FpArithNet.stageTest hd p) g bits := by
  let L := Stage.Links.layout hd
  have hgN : (linked d).ng = L.ng := (OrdModels.linked_model hd).ng
  induction g using Fin.addCases with
  | left g =>
    erw [links_old]
    have ho : bits.length = (gateEdges (FpArithNet.stageBase hd) g).length := by
      erw [links_old_edges,List.length_map] at hlen
      exact hlen
    erw [links_old_addresses]
    induction g using Fin.addCases with
    | left g =>
      erw [LocalGateEq.join_left,join_left_addresses]
      have he : bits.length = (gateEdges L g).length := by
        erw [join_left_edges,List.length_map] at ho
        exact ho
      have hg : g.val < L.ng := g.isLt
      simpa only [inner_stage,hgN,Fin.val_castAdd,if_pos hg,S8G.FpPhysicalAtom.stageTest] using fixed_linked_local hd p g bits he
    | right g =>
      erw [LocalGateEq.join_right]
      have hgl : g.val < d+1 := g.isLt
      simp only [inner_stage,hgN,Fin.val_castAdd,Fin.val_natAdd]
      change (if L.ng+g.val < L.ng then _ else if L.ng+g.val < L.ng+d+1 then _ else _) = _
      rw [if_neg (by omega),if_pos (by omega),Nat.add_sub_cancel_left]
      exact (range_local p g bits).symm
  | right g =>
    change inner_stage d p (L.ng+(d+1)+g.val) bits _ = _
    rw [inner_stage,hgN,if_neg (by omega),if_neg (by omega)]
    exact links_equal _ _ _ _ _ _ hlen

theorem stage_gate_local {d : ℕ} (hd : 1 ≤ d) (p start : ℕ) (first : Bool)
    (g : Fin (FpArithNet.boundedStage hd).ng) (bits : List Bool)
    (hlen : bits.length = (gateEdges (FpArithNet.boundedStage hd) g).length) :
    stageGate d p start g.val first bits =
      localCheck (FpArithNet.boundedStage hd) (if first then
        atPins (FpArithNet.stageTest hd p) (FpArithNet.operand hd false) (fun i => start.testBit i.val)
        else FpArithNet.stageTest hd p) g bits := by
  let A := FpArithNet.boundedStage hd
  have hp : localPorts (FpPolyDefs.stage d) g.val bits = addresses A g bits := local_ports (OrdModels.stage_model hd) g bits
  have he (j : Fin d) : (FpArithNet.operand hd false j).val = id j.val := OrdModels.input_val hd false j
  change (inner_stage d p g.val bits (localPorts (FpPolyDefs.stage d) g.val bits) &&
    (!first || pin d (localPorts (FpPolyDefs.stage d) g.val bits) id (fun j => start.testBit j))) = _
  rw [hp,inner_stage_local hd p g bits hlen]
  cases first with
  | false => simp
  | true =>
    simp only [Bool.not_true,Bool.false_or,if_true]
    exact (local_pins A (FpArithNet.stageTest hd p) (FpArithNet.operand hd false) (fun i => start.testBit i.val)
      id start.testBit he (fun _ => rfl) g bits hlen).symm

end DetDLP.M3A.OrdPorts
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP.M3A.OrdPorts

open S8C S8J S8H0 S8H0.GateAgree S8L.FpPair.Stage.Links FpPolyDefs
open S8H.PointAddresses S8L.FpPair.Address S8G.FpPhysicalAtom
attribute [-simp] Fin.natAdd_eq_addNat

def inner_physical (d p T g : ℕ) (bits : List Bool) (ps : List (ℕ × Bool)) :=
  let L := (linked d).ng
  if g < L then linkedGate d g bits && stagePins d p ps else if g < L+8*(d+1) then
    rows d p T (g-L) bits else equal bits

theorem physical_gate_local {d : ℕ} (hd : 1 ≤ d) (p T : ℕ)
    (g : Fin (S8G.FpPhysicalAtom.layout d hd).ng) (bits : List Bool)
    (hlen : bits.length = (gateEdges (S8G.FpPhysicalAtom.layout d hd) g).length) :
    inner_physical d p T g.val bits (addresses (S8G.FpPhysicalAtom.layout d hd) g bits) =
      localCheck (S8G.FpPhysicalAtom.layout d hd) (S8G.FpPhysicalAtom.test d hd p (min T p)) g bits := by
  let L := S8L.FpPair.Stage.Links.layout hd
  have hgN : (linked d).ng = L.ng := (OrdModels.linked_model hd).ng
  induction g using Fin.addCases with
  | left g =>
    erw [links_old,links_old_addresses]
    have ho : bits.length = (gateEdges (S8G.FpPhysicalAtom.base d hd) g).length := by
      erw [links_old_edges,List.length_map] at hlen
      exact hlen
    induction g using Fin.addCases with
    | left g =>
      erw [LocalGateEq.join_left,join_left_addresses]
      have he : bits.length = (gateEdges L g).length := by
        erw [join_left_edges,List.length_map] at ho
        exact ho
      have hg : g.val < L.ng := g.isLt
      simpa only [inner_physical,hgN,Fin.val_castAdd,if_pos hg] using fixed_linked_local hd p g bits he
    | right g =>
      erw [LocalGateEq.join_right]
      have hgl : g.val < 8*(d+1) := g.isLt
      change inner_physical d p T (L.ng+g.val) bits _ = _
      rw [inner_physical,hgN,if_neg (by omega),if_pos (by omega),Nat.add_sub_cancel_left]
      exact strip_local p T g bits
  | right g =>
    change inner_physical d p T (L.ng+8*(d+1)+g.val) bits _ = _
    rw [inner_physical,hgN,if_neg (by omega),if_neg (by omega)]
    exact links_equal _ _ _ _ _ _ hlen

theorem seeded_gate_local {d : ℕ} (hd : 1 ≤ d) (p T slope intercept : ℕ)
    (g : Fin (S8G.FpPhysicalAtom.layout d hd).ng) (bits : List Bool)
    (hlen : bits.length = (gateEdges (S8G.FpPhysicalAtom.layout d hd) g).length) :
    let ps := addresses (S8G.FpPhysicalAtom.layout d hd) g bits
    (inner_physical d p T g.val bits ps &&
      pin d ps (fun j => (linked d).nb+4*j) slope.testBit &&
      pin d ps (fun j => (linked d).nb+4*(5*(d+1)+j)+1) intercept.testBit) =
        localCheck (S8G.FpPhysicalAtom.layout d hd) (FpSlotTile.seedTest hd p T slope intercept) g bits := by
  have ha (j : Fin d) : (aWire hd j).val = (linked d).nb+4*j.val := by
    rw [(OrdModels.linked_model hd).nb]
    simp [aWire,S8G.FpPhysicalAtom.port,S8G.FpPhysicalAtom.col,AddLayout.reg,finProdFinEquiv_apply_val]
  have hb (j : Fin d) : (bWire hd j).val = (linked d).nb+4*(5*(d+1)+j.val)+1 := by
    rw [(OrdModels.linked_model hd).nb]
    simp [bWire,S8G.FpPhysicalAtom.port,S8G.FpPhysicalAtom.col,AddLayout.reg,finProdFinEquiv_apply_val]
    ring
  dsimp only
  unfold FpSlotTile.seedTest
  erw [local_pins _ _ (bWire hd) _ (fun j => (linked d).nb+4*(5*(d+1)+j)+1) intercept.testBit
      hb (fun _ => rfl) g bits hlen,
    local_pins _ _ (aWire hd) _ (fun j => (linked d).nb+4*j) slope.testBit
      ha (fun _ => rfl) g bits hlen]
  rw [physical_gate_local hd p T g bits hlen]

theorem anchor_edges {n : ℕ} (g : Fin n) : gateEdges (AnchoredLayout.anchors n) g = [g] := by
  change (List.finRange n).filter (fun i => decide (i=g)) = [g]
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·)) ((List.pairwise_lt_finRange _).filter _) (by simp)
  simp

theorem slot_gate_local {d k : ℕ} (hd : 1 ≤ d) (p T slope intercept : ℕ)
    (g : Fin (FpSlotTile.slotLayout d k hd).ng) (bits : List Bool)
    (hlen : bits.length = (gateEdges (FpSlotTile.slotLayout d k hd) g).length) :
    slotGate d k p T slope intercept g.val bits =
      localCheck (FpSlotTile.slotLayout d k hd) (FpSlotTile.slotTest hd p T slope intercept) g bits := by
  let P := S8G.FpPhysicalAtom.layout d hd
  let E := (linked d).ng + 8*(d+1)
  let ph := E+3*d+5*(d+1)
  have hp : ph = P.ng := by
    rw [show P.ng = (S8L.FpPair.Stage.Links.layout hd).ng+8*(d+1)+(3*d+5*(d+1)) from rfl]
    dsimp only [ph,E]
    rw [(OrdModels.linked_model hd).ng]
    omega
  let A := FpSlotTile.slotLayout d k hd
  change Fin A.ng at g
  have hports (u : Fin A.ng) : localPorts (slot d k) u.val bits = addresses A u bits := local_ports (FpSlotTile.slot_models hd) u bits
  let inner (u : ℕ) (ps : List (ℕ × Bool)) := inner_physical d p T u bits ps &&
    pin d ps (fun j => (linked d).nb+4*j) slope.testBit &&
    pin d ps (fun j => (linked d).nb+4*(5*(d+1)+j)+1) intercept.testBit
  change (if g.val<ph then inner g.val (localPorts (slot d k) g.val bits) else
    if g.val<ph+k then decide (g.val-ph<d+1) || !(bit bits 0) else equal bits) = _
  rw [hports,hp]
  induction g using Fin.addCases with
  | left g =>
    erw [links_old,links_old_addresses]
    have ho : bits.length = (gateEdges (FpSlotTile.body d k hd) g).length := by
      erw [links_old_edges,List.length_map] at hlen
      exact hlen
    induction g using Fin.addCases with
    | left g =>
      erw [LocalGateEq.join_left,join_left_addresses]
      have he : bits.length = (gateEdges P g).length := by
        erw [join_left_edges,List.length_map] at ho
        exact ho
      have hg : g.val < P.ng := g.isLt
      simp only [Fin.val_castAdd,if_pos hg]
      exact seeded_gate_local hd p T slope intercept g bits he
    | right g =>
      erw [LocalGateEq.join_right]
      have hl : g.val < k := g.isLt
      change (if P.ng+g.val<P.ng then _ else if P.ng+g.val<P.ng+k then _ else _) = _
      rw [if_neg (by omega),if_pos (by omega)]
      change (decide (P.ng+g.val-P.ng<d+1) || !(bit bits 0)) = _
      rw [Nat.add_sub_cancel_left]
      change (decide (g.val<d+1) || !(bit bits 0)) =
        (if g.val<d+1 then true else !(bits.getD ((gateEdges (AnchoredLayout.anchors k) g).idxOf g) false))
      rw [anchor_edges]
      by_cases h : g.val < d+1 <;> simp [h,bit]
  | right g =>
    change (if P.ng+k+g.val<P.ng then _ else if P.ng+k+g.val<P.ng+k then _ else _) = _
    rw [if_neg (by omega),if_neg (by omega)]
    exact links_equal _ _ _ _ _ _ hlen

end DetDLP.M3A.OrdPorts
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP.M3A.OrdPorts

open S8J S8H0 S8H0.GateAgree S8G.FpMoment FpPolyDefs
attribute [-simp] Fin.natAdd_eq_addNat

def slot_value (d k m p T : ℕ) (slope intercept : ℕ → ℕ) (u : ℕ) (bits : List Bool) :=
  let N := (slot d k).ng
  let i := (u/N)%m
  slotGate d k p T (slope i) (intercept i) (u%N) bits

def step_value (d m p P : ℕ) (u : ℕ) (bits : List Bool) :=
  let N := (FpPolyDefs.stage d).ng
  let j := u/N
  stageGate d p (if j<2*m then P else 1) (u%N) (decide (j%(2*m)=0)) bits

def chain_value (d k m p T P : ℕ) (slope intercept : ℕ → ℕ) (g : ℕ) (bits : List Bool) :=
  let n := 4*m*(slot d k).ng
  if g<n then slot_value d k m p T slope intercept g bits else if g<n+4*m*(FpPolyDefs.stage d).ng
    then step_value d m p P (g-n) bits else equal bits

theorem tile_divmod {m n : ℕ} (i : Fin m) (j : Fin n) :
    (finProdFinEquiv (i,j)).val/n = i.val ∧ (finProdFinEquiv (i,j)).val%n = j.val := by
  exact ⟨congrArg (fun z : Fin m × Fin n => z.1.val) (finProdFinEquiv.symm_apply_apply (i,j)),
    congrArg (fun z : Fin m × Fin n => z.2.val) (finProdFinEquiv.symm_apply_apply (i,j))⟩

theorem stage_bank {d m : ℕ} (hd : 1 ≤ d) (p P : ℕ) (b : Bool) (i : Fin (2*m))
    (g : Fin (FpArithNet.boundedStage hd).ng) (bits : List Bool)
    (hlen : bits.length = (gateEdges (FpArithNet.boundedStage hd) g).length) :
    let N := (FpArithNet.boundedStage hd).ng
    step_value d m p P ((if b then (2*m)*N else 0)+(finProdFinEquiv (i,g)).val) bits =
      localCheck (FpArithNet.boundedStage hd) (if i.val=0 then
        S8L.FpPair.Stage.Links.atPins (FpArithNet.stageTest hd p) (FpArithNet.operand hd false)
          (fun j => (if b then 1 else P).testBit j.val) else FpArithNet.stageTest hd p) g bits := by
  let N := (FpArithNet.boundedStage hd).ng
  have hn : 0 < N := lt_of_le_of_lt (Nat.zero_le _) g.isLt
  have hN : (FpPolyDefs.stage d).ng = N := (OrdModels.stage_model hd).ng
  have hi := i.isLt
  let u := (finProdFinEquiv (i,g)).val
  have hdiv : u/N=i.val := (tile_divmod i g).1
  have hmod : u%N=g.val := (tile_divmod i g).2
  dsimp only
  cases b with
  | false =>
    simp only [Bool.false_eq_true,if_false,zero_add,step_value,hN]
    change stageGate d p (if u/N<2*m then P else 1) (u%N) (decide (u/N%(2*m)=0)) bits = _
    rw [hdiv,hmod,if_pos hi,Nat.mod_eq_of_lt hi]
    simpa only [decide_eq_true_eq] using stage_gate_local hd p P (decide (i.val=0)) g bits hlen
  | true =>
    have hd' : ((2*m)*N+u)/N = 2*m+i.val := by
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,hdiv,Nat.add_comm]
    have hm' : ((2*m)*N+u)%N = g.val := by
      rw [Nat.add_comm,Nat.add_mul_mod_self_right,hmod]
    simp only [if_true,step_value,hN]
    change stageGate d p (if ((2*m)*N+u)/N<2*m then P else 1) (((2*m)*N+u)%N)
      (decide (((2*m)*N+u)/N%(2*m)=0)) bits = _
    rw [hd',hm',if_neg (show ¬2*m+i.val<2*m by omega),Nat.add_mod_left,Nat.mod_eq_of_lt hi]
    simpa only [decide_eq_true_eq] using stage_gate_local hd p 1 (decide (i.val=0)) g bits hlen

theorem chain_gate_local {d m k p : ℕ} [Fact p.Prime] (hd : 1 ≤ d) (T P : ℕ) (seed : FpSeed p m)
    (slope intercept : ℕ → ℕ)
    (hs : ∀ i : Fin m, slope i.val=(seed i).1.val ∧ intercept i.val=(seed i).2.val)
    (g : Fin (FpArithNet.chains hd m k).ng) (bits : List Bool)
    (hlen : bits.length = (gateEdges (FpArithNet.chains hd m k) g).length) :
    chain_value d k m p T P slope intercept g.val bits =
      localCheck (FpArithNet.chains hd m k) (FpArithNet.chainTest hd p T P seed) g bits := by
  let S := FpSlotTile.slotLayout d k hd
  let B := FpArithNet.boundedStage hd
  let n := 4*m*S.ng
  let bank := (2*m)*B.ng
  have hS : (slot d k).ng = S.ng := (FpSlotTile.slot_models hd).ng
  have hB : (FpPolyDefs.stage d).ng = B.ng := (OrdModels.stage_model hd).ng
  have hfour : 4*m*B.ng = bank+bank := by dsimp [bank]; ring
  induction g using Fin.addCases with
  | left g =>
    erw [links_old]
    have ho : bits.length = (gateEdges (FpArithNet.base hd m k) g).length := by
      erw [links_old_edges,List.length_map] at hlen
      exact hlen
    induction g using Fin.addCases with
    | left u =>
      erw [LocalGateEq.join_left]
      obtain ⟨⟨i,g⟩,rfl⟩ := finProdFinEquiv.surjective u
      erw [tile_local]
      have he : bits.length = (gateEdges S g).length := by
        erw [join_left_edges,List.length_map,tile_edges,List.length_map] at ho
        exact ho
      let v := (finProdFinEquiv (i,g)).val
      have hb : v < n := (finProdFinEquiv (i,g)).isLt
      have hj := hs (FpArithNet.blockIndex i)
      change slope (i.val%m) = _ ∧ intercept (i.val%m) = _ at hj
      have hd' : v/S.ng=i.val := (tile_divmod i g).1
      have hm' : v%S.ng=g.val := (tile_divmod i g).2
      rw [chain_value,hS]
      change (if v<n then _ else _) = _
      rw [if_pos hb,slot_value,hS]
      change slotGate d k p T (slope (v/S.ng%m)) (intercept (v/S.ng%m)) (v%S.ng) bits = _
      rw [hd',hm',hj.1,hj.2]
      exact slot_gate_local hd p T _ _ g bits he
    | right u =>
      erw [LocalGateEq.join_right]
      have h₂ : bits.length = (gateEdges (join (tiles (2*m) B) (tiles (2*m) B)) u).length := by
        erw [join_right_edges,List.length_map] at ho
        exact ho
      have hu : u.val < bank+bank := u.isLt
      change chain_value d k m p T P slope intercept (n+u.val) bits = _
      rw [chain_value,hS,hB,hfour]
      change (if n+u.val<n then _ else if n+u.val<n+(bank+bank) then _ else _) = _
      rw [if_neg (by omega),if_pos (by omega),Nat.add_sub_cancel_left]
      induction u using Fin.addCases with
      | left u =>
        erw [LocalGateEq.join_left]
        obtain ⟨⟨i,g⟩,rfl⟩ := finProdFinEquiv.surjective u
        erw [tile_local]
        have he : bits.length = (gateEdges B g).length := by
          erw [join_left_edges,List.length_map,tile_edges,List.length_map] at h₂
          exact h₂
        have h := stage_bank hd p P false i g bits he
        simp only [Bool.false_eq_true,if_false,zero_add] at h
        exact h
      | right u =>
        erw [LocalGateEq.join_right]
        obtain ⟨⟨i,g⟩,rfl⟩ := finProdFinEquiv.surjective u
        erw [tile_local]
        have he : bits.length = (gateEdges B g).length := by
          erw [join_right_edges,List.length_map,tile_edges,List.length_map] at h₂
          exact h₂
        exact stage_bank hd p P true i g bits he
  | right g =>
    change chain_value d k m p T P slope intercept (n+(bank+bank)+g.val) bits = _
    rw [chain_value,hS,hB,hfour]
    change (if n+(bank+bank)+g.val<n then _ else if n+(bank+bank)+g.val<n+(bank+bank) then _ else _) = _
    rw [if_neg (by omega),if_neg (by omega)]
    exact links_equal _ _ _ _ _ _ hlen

end DetDLP.M3A.OrdPorts
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP.M3A.OrdPorts

open S8J S8H0 S8H0.GateAgree S8G.FpMoment FpPolyDefs
attribute [-simp] Fin.natAdd_eq_addNat

theorem arith_gate_local {p m' D K T : ℕ} [Fact p.Prime] (hd : 1 ≤ D)
    (w η : W) (P : ℕ) (seed : FpSeed p m') (hm : m w=m') (hD : d w=D) (hK : k w=K)
    (hp : pre w=η) (hpr : prime w=p) (hT : threshold w=T) (hP : target w=P)
    (hs : ∀ i : Fin m', (nums (field w 1)).getD (2*i.val) 0-1=(seed i).1.val ∧
      (nums (field w 1)).getD (2*i.val+1) 0=(seed i).2.val)
    (g : Fin (FpArithNet.arith hd m' K η).ng) (bits : List Bool)
    (hlen : bits.length = (gateEdges (FpArithNet.arith hd m' K η) g).length) :
    ordinary w g.val bits = localCheck (FpArithNet.arith hd m' K η) (FpArithNet.arithTest hd p T P seed η) g bits := by
  let C := FpArithNet.chains hd m' K
  let A := FpSlotTile.slotLayout D K hd
  let B := FpArithNet.boundedStage hd
  let np := min η.length (4*m'*D)
  let a (i : ℕ) := (nums (field w 1)).getD (2*i) 0-1
  let b (i : ℕ) := (nums (field w 1)).getD (2*i+1) 0
  have hA : (slot D K).ng=A.ng := (FpSlotTile.slot_models hd).ng
  have hB : (FpPolyDefs.stage D).ng=B.ng := (OrdModels.stage_model hd).ng
  have hc : (chains m' D K).ng=C.ng := OrdModels.chain_gate_count hd
  have hend : 4*m'*(slot D K).ng+4*m'*(FpPolyDefs.stage D).ng ≤ C.ng := by
    change _ ≤ (4*m'*A.ng+(2*m'*B.ng+2*m'*B.ng))+(4*m'*D+4*m'*D)
    rw [hA,hB,show 4*m'*B.ng=2*m'*B.ng+2*m'*B.ng by ring]
    omega
  have hword (u : ℕ) : ordinary w u bits =
      if u<C.ng then chain_value D K m' p T P a b u bits else if u<C.ng+np
      then bit bits 0 == bit η (u-C.ng) else if u=C.ng+np then decide (η.length ≤ 4*m'*D ∧ bit bits 0=false)
      else equal bits := by
    simp only [ordinary,hm,hD,hK,hp,hpr,hT,hP,hc]
    unfold chain_value slot_value step_value
    dsimp only [a,b,np]
    split_ifs <;> first | rfl | omega
  rw [hword]
  induction g using Fin.addCases with
  | left u =>
    erw [links_old]
    have ho : bits.length = (gateEdges (FpArithNet.pinBase hd m' K η) u).length := by
      erw [links_old_edges,List.length_map] at hlen
      exact hlen
    induction u using Fin.addCases with
    | left g =>
      erw [LocalGateEq.join_left]
      have hgl : g.val<C.ng := g.isLt
      simp only [Fin.val_castAdd,if_pos hgl]
      have he : bits.length=(gateEdges C g).length := by
        erw [join_left_edges,List.length_map] at ho
        exact ho
      exact chain_gate_local hd T P seed a b hs g bits he
    | right i =>
      erw [LocalGateEq.join_right]
      have hi : i.val < np+1 := i.isLt
      change (if C.ng+i.val<C.ng then _ else if C.ng+i.val<C.ng+np then
        bit bits 0 == bit η (C.ng+i.val-C.ng) else if C.ng+i.val=C.ng+np then _ else _) =
        (if i.val<np then decide (bits.getD ((gateEdges (AnchoredLayout.anchors (np+1)) i).idxOf i) false=η[i.val]?.getD false)
          else decide (η.length≤4*m'*D ∧ bits.getD ((gateEdges (AnchoredLayout.anchors (np+1)) i).idxOf i) false=false))
      rw [anchor_edges,if_neg (by omega),Nat.add_sub_cancel_left]
      by_cases h : i.val<np
      · rw [if_pos (by omega),if_pos h]
        simp [bit,List.getD_eq_getElem?_getD,Bool.beq_eq_decide_eq]
      · rw [if_neg (by omega),if_pos (by omega),if_neg h]
        simp [bit]
  | right i =>
    change (if C.ng+(np+1)+i.val<C.ng then _ else if C.ng+(np+1)+i.val<C.ng+np then _
      else if C.ng+(np+1)+i.val=C.ng+np then _ else _) = _
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    exact links_equal _ _ _ _ _ _ hlen

end DetDLP.M3A.OrdPorts
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
open DetDLP DetDLP.M3A DetDLP.M3A.FpPolyDefs S8J S8H.PointAddresses

open DetDLP.w4_M5Network DetDLP.S8H0.GateAgree
attribute [-simp] Fin.natAdd_eq_addNat

private theorem indicator_spec (P n : ℕ) (hp : 0 < P) (hn : 0 < n) (b : Bool) :
    EncodesTruncPoly P n (indicator n b) (if b then 1 else 0) := by
  classical
  let c (i : Fin n) := if i.val = 0 then b.toNat else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · have h : 1 < 2^P := Nat.one_lt_pow (by omega) (by decide)
    intro i; cases b <;> simp [c] <;> (split <;> omega)
  · unfold indicator
    congr 1
    rw [List.ofFn_eq_map, show List.range n = (List.finRange n).map Fin.val by simp, List.map_map]; rfl
  · cases b with
    | false => simp [truncPolyOfCoeffs,c]
    | true =>
      let z : Fin n := ⟨0,hn⟩
      unfold truncPolyOfCoeffs
      rw [Finset.sum_eq_single z]
      · simp [z,c,Polynomial.monomial_zero_left]
      · intro i _ h; have hi : i.val ≠ 0 := fun e => h (Fin.ext e); simp [c,hi]
      · simp
theorem DetDLP.M3A.FpPolyDefs.ordinary_of_localCheck
    {p m' D K T : ℕ} [Fact p.Prime] (hd : 1 ≤ D)
    (q : w3_Query) (w η : W) (Pval : ℕ) (seed : FpSeed p m')
    (sl : Fin (FpArithNet.layout hd m' K η).ng ≃ (w3_lookupSlot q ⊕ Fin (FpArithNet.arith hd m' K η).ng))
    (addr : (v : Fin (w3_factorGraph (FpArithNet.layout hd m' K η)).nV) →
      (Fin ((w3_factorGraph (FpArithNet.layout hd m' K η)).deg v) → Bool) → ℕ)
    (hP : 0 < w3_precision q)
    (hm : m w = m') (hD : d w = D) (hK : k w = K) (hpre : pre w = η)
    (hlen : len w = w3_len q)
    (hsl : ∀ g : Fin (FpArithNet.arith hd m' K η).ng, sl (Fin.castAdd (4 * m') g) = .inr g)
    (g : Fin (FpArithNet.arith hd m' K η).ng)
    (a : Fin ((w3_factorGraph (FpArithNet.layout hd m' K η)).subdivision.deg
      ((w3_factorGraph (FpArithNet.layout hd m' K η)).oldVertex
        (Fin.castAdd (FpArithNet.layout hd m' K η).nb (Fin.castAdd (4 * m') g)))) → Bool)
    (hcheck : ordinary w g.val (List.ofFn a) = localCheck (FpArithNet.arith hd m' K η)
      (FpArithNet.arithTest hd p T Pval seed η) g (List.ofFn a)) :
    let L := FpArithNet.layout hd m' K η
    let G := w3_factorGraph L
    let v := G.oldVertex (Fin.castAdd L.nb (Fin.castAdd (4 * m') g))
    EncodesTruncPoly (w3_precision q) (w3_len q) (fpEntry (encodePortQuery w v.val (List.ofFn a)))
      (w3_liftTensor G (w3_gateWeight (w3_incSlot L sl) addr (w3_factorChecks L (FpArithNet.test hd p T Pval seed η))) v a) := by
  let A := FpArithNet.arith hd m' K η
  let L := FpArithNet.layout hd m' K η
  let G := w3_factorGraph L
  let v := Fin.castAdd L.nb (Fin.castAdd (4*m') g)
  let t : w3_factorTest L := FpArithNet.test hd p T Pval seed η
  have check : ordinary w g.val (List.ofFn a) = w3_factorChecks L t v (fun j => a (G.oldPort v j)) := by
    rw [hcheck]
    calc
      _ = localCheck L t (Fin.castAdd (4*m') g) (List.ofFn a) :=
        (OrdPorts.lookup_old A (FpArithNet.bus hd η) (FpArithNet.arithTest hd p T Pval seed η) g _).symm
      _ = _ := (local_eq L t (Fin.castAdd (4*m') g) a).trans (G.subdivisionTensor_oldVertex _ v a)
  have slotId : w3_incSlot L sl v = .inr (Fin.castAdd L.nb g) := by
    unfold w3_incSlot
    simp only [Equiv.trans_apply,v]
    erw [finSumFinEquiv_symm_apply_castAdd]
    simp only [Equiv.sumCongr_apply, Sum.map_inl]
    erw [hsl g]
    rfl
  have count := OrdModels.whole_gate_count (M:=m') (K:=K) hd η
  have hn : (whole (m w) (d w) (k w) (pre w).length).ng - 4*m w = A.ng := by
    rw [hm,hD,hK,hpre,count]
    change A.ng+4*m'-4*m'=A.ng
    omega
  have hlt : g.val < A.ng := g.isLt
  have entry : fpEntry (encodePortQuery w (G.oldVertex v).val (List.ofFn a)) =
      indicator (len w) (ordinary w g.val (List.ofFn a)) := by
    change fpEntry (encodePortQuery w g.val (List.ofFn a)) = _
    simp [fpEntry,encodePortQuery,DetDLP_W1_Queries.second,DetDLP_W1_Queries.third,hn,hlt]
  have lift : w3_liftTensor G (w3_gateWeight (w3_incSlot L sl) addr (w3_factorChecks L t)) (G.oldVertex v) a =
      (if ordinary w g.val (List.ofFn a) then 1 else 0) := by
    unfold w3_liftTensor WireGraph.oldVertex
    erw [Fin.addCases_left]
    unfold w3_gateWeight
    erw [slotId]
    rw [check]
  dsimp only
  rw [entry,lift]
  have H := indicator_spec (w3_precision q) (len w) hP (Nat.zero_lt_succ _) (ordinary w g.val (List.ofFn a))
  rw [hlen] at H
  simpa only [hlen] using H
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open DetDLP DetDLP.M3A DetDLP.M3A.FpPolyDefs S8J S8H.PointAddresses

theorem DetDLP.M3A.FpPolyDefs.fpEntry_ordinary_vertex
    {p m' D K T : ℕ} [Fact p.Prime] (hd : 1 ≤ D)
    (q : w3_Query) (w η : W) (Pval : ℕ) (seed : FpSeed p m')
    (sl : Fin (FpArithNet.layout hd m' K η).ng ≃ (w3_lookupSlot q ⊕ Fin (FpArithNet.arith hd m' K η).ng))
    (addr : (v : Fin (w3_factorGraph (FpArithNet.layout hd m' K η)).nV) →
      (Fin ((w3_factorGraph (FpArithNet.layout hd m' K η)).deg v) → Bool) → ℕ)
    (hP : 0 < w3_precision q)
    (hm : m w = m') (hD : d w = D) (hK : k w = K) (hpre : pre w = η)
    (hpr : prime w = p) (hth : threshold w = T) (htg : target w = Pval) (hlen : len w = w3_len q)
    (hseed : ∀ i : Fin m',
      (nums (field w 1)).getD (2 * i.val) 0 - 1 = (seed i).1.val ∧
      (nums (field w 1)).getD (2 * i.val + 1) 0 = (seed i).2.val)
    (hsl : ∀ g : Fin (FpArithNet.arith hd m' K η).ng, sl (Fin.castAdd (4 * m') g) = .inr g)
    (g : Fin (FpArithNet.arith hd m' K η).ng)
    (a : Fin ((w3_factorGraph (FpArithNet.layout hd m' K η)).subdivision.deg
      ((w3_factorGraph (FpArithNet.layout hd m' K η)).oldVertex
        (Fin.castAdd (FpArithNet.layout hd m' K η).nb (Fin.castAdd (4 * m') g)))) → Bool) :
    let L := FpArithNet.layout hd m' K η
    let G := w3_factorGraph L
    let v := G.oldVertex (Fin.castAdd L.nb (Fin.castAdd (4 * m') g))
    EncodesTruncPoly (w3_precision q) (w3_len q) (fpEntry (encodePortQuery w v.val (List.ofFn a)))
      (w3_liftTensor G (w3_gateWeight (w3_incSlot L sl) addr (w3_factorChecks L (FpArithNet.test hd p T Pval seed η))) v a) := by
  let A := FpArithNet.arith hd m' K η
  let L := FpArithNet.layout hd m' K η
  have hE : S8H0.GateAgree.gateEdges L (Fin.castAdd (4*m') g) =
      (S8H0.GateAgree.gateEdges A g).map (Fin.castAdd (4*m'*K)) := OrdPorts.firstFiber _ _ _
  have hl : (List.ofFn a).length = (S8H0.GateAgree.gateEdges A g).length := by
    have h := congrArg List.length (S8H0.GateAgree.gate_ports L (Fin.castAdd (4*m') g))
    rw [hE,List.length_map,List.length_map] at h
    exact List.length_ofFn.trans h
  apply ordinary_of_localCheck hd q w η Pval seed sl addr hP hm hD hK hpre hlen hsl g a
  exact OrdPorts.arith_gate_local hd w η Pval seed hm hD hK hpre hpr hth htg hseed g _ hl

abbrev solution := @DetDLP.M3A.FpPolyDefs.fpEntry_ordinary_vertex
end
