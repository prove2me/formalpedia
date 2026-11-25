-- Prove2me | solution 2 for DetDLP.w3_ec_separator_btn
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T12:03:01.213842+00:00
-- url     : https://prove2.me/submissions/911bd096-4731-4e12-ad58-104703755115

import Definitions.Def_DetDLP_M3B_ECNetBijection
import Theorems.Thm_DetDLP_m3b_ec_body_degree
import Theorems.Thm_DetDLP_m3b_ec_layout_size
import Theorems.Thm_DetDLP_w3_native_lookup_address
import Theorems.Thm_DetDLP_m3b_ec_wire_core_exists
import Theorems.Thm_DetDLP_m3b_ec_entry_poly
import Theorems.Thm_DetDLP_m3b_ec_lookup_scan
import Theorems.Thm_DetDLP_m3b_ec_body_fits_core
import Theorems.Thm_DetDLP_m3b_ec_build_poly
import Theorems.Thm_DetDLP_m3b_ec_top_layout_models
import Theorems.Thm_DetDLP_m3b_ec_decoded_dimensions
import Theorems.Thm_DetDLP_w3_compile_wire_separator

section
section
set_option autoImplicit false
open DetDLP DetDLP.M3B DetDLP.M3B.ECCert DetDLP.M3B.ECPhysicalNet

private theorem physicalAddressEquivForProgram
    {p m k : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (seed : ECSeed p m) (T : ℕ) (P : Point E) (pre : List Bool)
    (F : Fin m → List (Point E)) (hT : T ≤ p) (hk : 2 * T ≤ 2 ^ k)
    (hF : ListsOK E F seed T) (hp : 3 < p) (hm : 1 ≤ m) :
    ∃ e : Accepted (k := k) E seed T P pre ≃
        {t : Tuples E F // (base E F).tupleVal t.2 = (base E F).tupleVal t.1 + P ∧
          prefixOK E F pre t},
      (∀ x, (e x).val = tuple E seed T P pre F hT hk hF x) ∧
      ∀ x (b : Fin m) (j : Fin 2) (s : Bool),
        bitsToNat (fun l : Fin k => x.val ((busAddr (ix s (pointIdx b j)) 1
          (Fin.castLE (le_max_right _ _) l)).index.castSucc.castAdd
            (body (k := k) E seed T P pre).core.A.ne)) =
          ECAddress.address E seed T b
            ((F b).get (if s then (e x).val.2 b j else (e x).val.1 b j)) := by
  refine ⟨ECNetBijection.acceptEquiv E seed T P pre F hT hk hF hp hm,
    ECNetBijection.acceptEquiv_tuple E seed T P pre F hT hk hF hp hm, ?_⟩
  intro x b j s
  exact ECPhysicalNet.physical_address E seed T P pre F hT hk hF x b j s

end

section
section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace DetDLP.M3B.ECNonlookupPorts
open w4_M5Network S8J S8H0
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


open S8J.CircuitRealizes in
theorem cycle_local {k : ℕ} (B : Block) (W : Wiring B.A.ne k) (g : Fin B.A.ng) (a : List Bool) :
    localCheck (circuit B W) (test B W) (Fin.castAdd B.A.ne g) a = localCheck B.A B.t g a := by
  let n := B.A.ne
  let U := circuit B W
  let pred := fun e : Fin (n+(n+n)) => @decide _ ((inferInstance : DecidableEq (Fin (B.A.ng+n))) (U.gate e) (Fin.castAdd n g))
  have hl (e : Fin n) : (pred ∘ Fin.castAdd (n+n)) e = decide (B.A.gate e = g) := by
    simp only [Function.comp_apply,pred,U,n,circuit,S8H.CopyCycle.layout,Fin.addCases_left,Fin.castAdd_inj]
  have hr (e : Fin (n+n)) : (pred ∘ Fin.natAdd n) e = false := by
    induction e using Fin.addCases <;> simp only [Function.comp_apply,pred,U,n,circuit,S8H.CopyCycle.layout,
      Fin.addCases_right,Fin.addCases_left,disjoint_parts,decide_false]
  have he : gateEdges U (Fin.castAdd n g) = (gateEdges B.A g).map (Fin.castAdd (n+n)) := by
    change (List.finRange (n+(n+n))).filter pred = _
    rw [split_range, List.filter_append, List.filter_map, List.filter_map]
    have hnil : (List.finRange (n+n)).filter (pred ∘ Fin.natAdd n) = [] :=
      List.filter_eq_nil_iff.mpr (fun x _ => by rw [hr]; decide)
    rw [List.filter_congr (fun x _ => hl x), hnil, List.map_nil, List.append_nil]; rfl
  simp only [localCheck, test, S8H.CopyCycle.checks, Fin.addCases_left]
  congr 1; funext e
  change a.getD ((gateEdges U (Fin.castAdd n g)).idxOf (Fin.castAdd (n+n) e.val)) false = _
  rw [he,idx_map _ (fun _ _ h => Fin.castAdd_inj.mp h)]


def agree (a : List Bool) := a.all (· == true) || a.all (· == false)

private theorem agree_iff {n : ℕ} (a : Fin n → Bool) (k : Fin n) :
    agree (List.ofFn a) = true ↔ ∀ i, a i = a k := by
  simp only [agree,Bool.or_eq_true,List.all_eq_true,List.mem_ofFn,beq_iff_eq,forall_exists_index,forall_apply_eq_imp_iff]
  constructor
  · rintro (h|h) i <;> rw [h i,h k]
  · intro h; cases h' : a k <;> simp [h,h']

/-- A subdivision edge reads both, and only, the two halves of its wire. -/
theorem edge_eq (G : WireGraph) (T) (e : Fin G.nE) (a) : agree (List.ofFn a) =
    G.subdivisionTensor T (G.equalityVertex e) a := by
  apply Bool.eq_iff_iff.mpr
  rw [agree_iff a (G.equalityRightPort e),WireGraph.subdivisionTensor_equalityVertex,decide_eq_true_eq]
  constructor
  · exact fun h => h _
  · intro h i
    have H := (G.mem_equalityPorts_iff e _).mp (List.get_mem _ i)
    have inj : Function.Injective (G.subdivision.ports (G.equalityVertex e)).get := fun _ _ => (G.subdivision_ports_nodup _).get_inj_iff.mp
    rcases H with hl|hr
    · exact (congrArg a (inj (hl.trans (G.get_equalityLeftPort e).symm))).trans h
    · exact congrArg a (inj (hr.trans (G.get_equalityRightPort e).symm))

/-- At a bit vertex the designated representative and the full port fibre give the same equality check. -/
theorem bit_eq (A : w3_FactorLayout) (T : w3_factorTest A) (b : Fin A.nb) (a) :
    let G := w3_factorGraph A; let v := Fin.natAdd A.ng b
    agree (List.ofFn a) = G.subdivisionTensor (w3_factorChecks A T) (G.oldVertex v) a := by
  let G := w3_factorGraph A; let v := Fin.natAdd A.ng b
  let idx (e : {i : Fin A.ne // A.bit i = b}) := G.portIndex v e.val (w3_bitInc A b e.val e.property)
  let r := idx ⟨A.rep b,A.rep_bit b⟩
  apply Bool.eq_iff_iff.mpr
  rw [agree_iff a (G.oldPort v r),G.subdivisionTensor_oldVertex (w3_factorChecks A T) v a]
  simp only [v,w3_factorChecks,Fin.addCases_right,decide_eq_true_eq]
  constructor
  · exact fun h e => h _
  · intro h i
    obtain ⟨j,rfl⟩ := (G.oldPort_bijective v).surjective i
    let e := (G.ports v).get j
    have he := (G.mem_ports v e).mp (List.get_mem _ j)
    have hb : A.bit e = b := by
      rcases he with he|he <;> have hh := congrArg Fin.val he
      · change (A.gate e).val = A.ng + b.val at hh; have := (A.gate e).isLt; omega
      · apply Fin.ext; change A.ng + (A.bit e).val = A.ng + b.val at hh; omega
    have hj : idx ⟨e,hb⟩ = j := (G.ports_nodup v).get_inj_iff.mp (G.get_portIndex v e _)
    exact hj ▸ h ⟨e,hb⟩


open S8H.CopyCycle in
theorem cycle_eq {n g : ℕ} (own : Fin n → Fin g) (next : Equiv.Perm (Fin n)) (T) (b : Fin n) (a) :
    let A := layout own next; let G := w3_factorGraph A; let v := Fin.castAdd A.nb (Fin.natAdd g b)
    agree (List.ofFn a) = G.subdivisionTensor (w3_factorChecks A (checks own next T)) (G.oldVertex v) a := by
  let A := layout own next; let G := w3_factorGraph A; let u := Fin.natAdd g b; let v := Fin.castAdd n u
  let left := Fin.natAdd n (Fin.castAdd n b); let right := Fin.natAdd n (Fin.natAdd n b)
  have hl : A.gate left = u := by simp [A,left,u,layout, -Fin.natAdd_eq_addNat]
  have hr : A.gate right = u := by simp [A,right,u,layout, -Fin.natAdd_eq_addNat]
  let idx (e : Fin A.ne) (h : A.gate e = u) := G.oldPort v (G.portIndex v e (w3_gateInc A u e h))
  apply Bool.eq_iff_iff.mpr; rw [agree_iff a (idx right hr),G.subdivisionTensor_oldVertex _ v a]
  change (∀ i, a i = a (idx right hr)) ↔ w3_factorChecks A _ v _ = true
  simp only [A,layout,v,u,w3_factorChecks,Fin.addCases_left,S8H.CopyCycle.checks,Fin.addCases_right,decide_eq_true_eq]
  change (∀ i, a i = a (idx right hr)) ↔ a (idx left hl) = a (idx right hr)
  constructor
  · exact fun h => h _
  · intro h i; obtain ⟨j,rfl⟩ := (G.oldPort_bijective v).surjective i
    let e := (G.ports v).get j
    have he := (G.mem_ports v e).mp (List.get_mem _ j)
    have hu : A.gate e = u := by
      rcases he with he|he
      · exact Fin.castAdd_inj.mp he
      · have hh := congrArg Fin.val he; change A.ng+(A.bit e).val = u.val at hh; have := u.isLt; change g+n+_ = _ at hh; omega
    have eqs : ∀ f : Fin (n+(n+n)), A.gate f = u → f = left ∨ f = right := by
      intro f; induction f using Fin.addCases with
      | left k => intro h; have hh := congrArg Fin.val h; simp only [A,layout,Fin.addCases_left,Function.comp_apply,Fin.val_castAdd,u,Fin.val_natAdd] at hh; have := (own k).isLt; omega
      | right k => induction k using Fin.addCases with
        | left k =>
          intro h; left; have hh : k = b := by simpa [A,layout,u,-Fin.natAdd_eq_addNat] using h
          rw [hh]
        | right k =>
          intro h; right; have hh : k = b := by simpa [A,layout,u,-Fin.natAdd_eq_addNat] using h
          rw [hh]
    have hj : G.portIndex v e (w3_gateInc A u e hu) = j := (G.ports_nodup v).get_inj_iff.mp (G.get_portIndex v e _)
    rw [←hj]; change a (idx e hu) = _; rcases eqs e hu with H|H <;> simp only [H]; exact h


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


open S8J.CircuitRealizes in
theorem cycle_edges {k : ℕ} (B : Block) (W : Wiring B.A.ne k) (g : Fin B.A.ng) :
    gateEdges (circuit B W) (Fin.castAdd B.A.ne g) = (gateEdges B.A g).map (Fin.castAdd (B.A.ne+B.A.ne)) := by
  let n := B.A.ne
  let U := circuit B W
  let pred := fun e : Fin (n+(n+n)) => @decide _ ((inferInstance : DecidableEq (Fin (B.A.ng+n))) (U.gate e) (Fin.castAdd n g))
  have hl (e : Fin n) : (pred ∘ Fin.castAdd (n+n)) e = decide (B.A.gate e = g) := by
    simp only [Function.comp_apply,pred,U,n,circuit,S8H.CopyCycle.layout,Fin.addCases_left,Fin.castAdd_inj]
  have hr (e : Fin (n+n)) : (pred ∘ Fin.natAdd n) e = false := by
    induction e using Fin.addCases <;> simp only [Function.comp_apply,pred,U,n,circuit,S8H.CopyCycle.layout,
      Fin.addCases_right,Fin.addCases_left,disjoint_parts,decide_false]
  have he : gateEdges U (Fin.castAdd n g) = (gateEdges B.A g).map (Fin.castAdd (n+n)) := by
    change (List.finRange (n+(n+n))).filter pred = _
    rw [split_range, List.filter_append, List.filter_map, List.filter_map]
    have hnil : (List.finRange (n+n)).filter (pred ∘ Fin.natAdd n) = [] :=
      List.filter_eq_nil_iff.mpr (fun x _ => by rw [hr]; decide)
    rw [List.filter_congr (fun x _ => hl x), hnil, List.map_nil, List.append_nil]; rfl
  exact he

theorem lookup_edges (A : w3_FactorLayout) {n k : ℕ} (bus : Fin n → Fin k → Fin A.nb)
    (g : Fin A.ng) :
    gateEdges (ECLayout.layout A bus) (Fin.castAdd n g) = (gateEdges A g).map (Fin.castAdd (n*k)) :=
  firstFiber _ _ _

theorem gate_length (A : w3_FactorLayout) (g : Fin A.ng) :
    let G := w3_factorGraph A
    G.subdivision.deg (G.oldVertex (Fin.castAdd A.nb g)) = (gateEdges A g).length := by
  have h := congrArg List.length (gate_ports A g)
  erw [List.length_map] at h
  exact h

theorem fit_check {q : ℕ} {N : ECPolyDefs.N} {B : NamedBlocks.B q} (fit : ECFits.Fits N B)
    (g : Fin B.core.A.ng) (bs : List Bool) (hl : bs.length=(gateEdges B.core.A g).length) :
    ECPolyDefs.check N g.val bs = localCheck B.core.A B.core.t g bs := by
  let es := gateEdges B.core.A g
  let x (e : Fin B.core.A.ne) := bs.getD (es.idxOf e) false
  have hn : es.Nodup := (List.nodup_finRange _).filter _
  have he : es.map x = bs := by
    apply List.ext_getElem (by simp [es,hl])
    intro i h₁ h₂
    have hi : i < es.length := by simpa using h₁
    simp [x,hn.idxOf_getElem i hi,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h₂]
  exact (congrArg (ECPolyDefs.check N g.val) he).symm.trans (fit.chk g x)

open S8J.CircuitRealizes in
theorem copy_agree {k : ℕ} (B : Block) (W : Wiring B.A.ne k) (g : Fin B.A.ne) (bs : List Bool)
    (hlen : bs.length = (gateEdges (circuit B W) (Fin.natAdd B.A.ng g)).length) :
    agree bs = localCheck (circuit B W) (test B W) (Fin.natAdd B.A.ng g) bs := by
  let A := circuit B W
  let v := Fin.natAdd B.A.ng g
  let G := w3_factorGraph A
  let a (i : Fin (G.subdivision.deg (G.oldVertex (Fin.castAdd A.nb v)))) := bs.getD i.val false
  have hl : G.subdivision.deg (G.oldVertex (Fin.castAdd A.nb v)) = bs.length :=
    (gate_length A v).trans hlen.symm
  have he : List.ofFn a = bs := by
    apply List.ext_getElem (by simpa only [List.length_ofFn] using hl)
    intro i _ hi
    simp [a,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
  rw [←he]
  exact (cycle_eq B.A.gate W.next B.t g a).trans (local_eq A (test B W) v a).symm

end DetDLP.M3B.ECNonlookupPorts
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace DetDLP.M3B.ECNonlookup
open ECPolyDefs Groundwork ECNonlookupPorts w4_M5Network S8J
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [-simp] Fin.natAdd_eq_addNat

def ind (n : ℕ) (b : Bool) := encodeNatListBin ((List.range n).map (fun j => if b && j=0 then 1 else 0))
private theorem indicator_spec (P n : ℕ) (hp : 0 < P) (hn : 0 < n) (b : Bool) :
    EncodesTruncPoly P n (ind n b) (if b then 1 else 0) := by
  classical
  let c (i : Fin n) := if i.val = 0 then b.toNat else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · have h : 1 < 2^P := Nat.one_lt_pow (by omega) (by decide)
    intro i; cases b <;> simp [c] <;> split <;> omega
  · unfold ind
    congr 1
    rw [List.ofFn_eq_map, show List.range n = (List.finRange n).map Fin.val by simp, List.map_map]
    apply List.map_congr_left
    intro i _
    cases b <;> simp [c,Function.comp_def]
  · cases b with
    | false => simp [truncPolyOfCoeffs,c]
    | true =>
      let z : Fin n := ⟨0,hn⟩
      unfold truncPolyOfCoeffs
      rw [Finset.sum_eq_single z]
      · simp [z,c,Polynomial.monomial_zero_left]
      · intro i _ h; have hi : i.val ≠ 0 := fun e => h (Fin.ext e); simp [c,hi]
      · simp

theorem ind_spec (q : w3_Query) (b : Bool) : EncodesTruncPoly (w3_precision q) (w3_len q)
    (ind (w3_len q) b) (if b then 1 else 0) :=
  indicator_spec _ _ (by unfold w3_precision;omega) (by unfold w3_len;omega) b

theorem ind_transport (q : w3_Query) {w : W} {b t : Bool}
    (hw : w=ind (w3_len q) b) (ht : b=t) :
    EncodesTruncPoly (w3_precision q) (w3_len q) w (if t then 1 else 0) := by
  subst w
  subst t
  exact ind_spec q b

theorem arith_word (q : w3_Query) (hmeta : (ECPolyDefs.dimensions q.input).2.1=q.m ∧ (ECPolyDefs.dimensions q.input).2.2.2.2.2=w3_len q) (v : ℕ) (bs : W)
    (h : v<ng (compiled q.input)) :
    ecEntry (encodePortQuery q.input v bs) = ind (w3_len q) (check (compiled q.input) v bs) := by
  have hn := hmeta.2
  simp [ecEntry,encodePortQuery,DetDLP_W1_Queries.second,DetDLP_W1_Queries.third,h,hn,ind]

theorem equal_word (q : w3_Query) (hmeta : (ECPolyDefs.dimensions q.input).2.1=q.m ∧ (ECPolyDefs.dimensions q.input).2.2.2.2.2=w3_len q) (v : ℕ) (bs : W)
    (h : ¬v<ng (compiled q.input)) (h' : ¬ (ng (compiled q.input)+ne (compiled q.input)≤v ∧
      v<ng (compiled q.input)+ne (compiled q.input)+4*q.m)) :
    ecEntry (encodePortQuery q.input v bs) = ind (w3_len q) (agree bs) := by
  obtain ⟨hm,hn⟩ := hmeta
  simp [ecEntry,encodePortQuery,DetDLP_W1_Queries.second,DetDLP_W1_Queries.third,h,hm,hn,h',ind,agree]

end DetDLP.M3B.ECNonlookup
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace DetDLP.M3B.ECNonlookup
open S8J S8J.CircuitRealizes S8H0 ECPolyDefs ECNonlookupPorts w4_M5Network
attribute [-simp] Fin.natAdd_eq_addNat

section
variable (q : w3_Query) (hmeta : (ECPolyDefs.dimensions q.input).2.1=q.m ∧ (ECPolyDefs.dimensions q.input).2.2.2.2.2=w3_len q) (A : w3_FactorLayout)
    (bus : Fin (4*q.m) → Fin q.k → Fin A.nb) (t : w3_factorTest A)
    (sl : Fin (ECLayout.layout A bus).ng ≃ (w3_lookupSlot q ⊕ Fin A.ng))
    (addr : (v : Fin (w3_factorGraph (ECLayout.layout A bus)).nV) →
      (Fin ((w3_factorGraph (ECLayout.layout A bus)).deg v) → Bool) → ℕ)
local notation "L" => ECLayout.layout A bus
local notation "G" => w3_factorGraph L
local notation "tt" => ECLayout.test A bus t
local notation "weights" => w3_gateWeight (q:=q) (w3_incSlot (q:=q) L sl) addr (w3_factorChecks L tt)
local notation "c" => compiled q.input

theorem inner_length (g : Fin A.ng) (a : Fin ((G).subdivision.deg
    ((G).oldVertex (Fin.castAdd (L).nb (Fin.castAdd (4*q.m) g)))) → Bool) :
    (List.ofFn a).length = (gateEdges A g).length := by
  have H := gate_length L (Fin.castAdd (4*q.m) g)
  rw [lookup_edges,List.length_map] at H
  exact List.length_ofFn.trans H

theorem old_weight (hsl : ∀ g : Fin A.ng, sl (Fin.castAdd (4*q.m) g)=.inr g) (g : Fin A.ng)
    (a : Fin ((G).subdivision.deg ((G).oldVertex (Fin.castAdd (L).nb (Fin.castAdd (4*q.m) g)))) → Bool) :
    let v := (G).oldVertex (Fin.castAdd (L).nb (Fin.castAdd (4*q.m) g))
    w3_liftTensor G weights v a = (if localCheck A t g (List.ofFn a) then 1 else 0) := by
  dsimp only
  let u := Fin.castAdd (L).nb (Fin.castAdd (4*q.m) g)
  have slot : w3_incSlot L sl u = .inr (Fin.castAdd (L).nb g) := by
    unfold w3_incSlot
    simp only [Equiv.trans_apply,u]
    erw [finSumFinEquiv_symm_apply_castAdd]
    simp only [Equiv.sumCongr_apply,Sum.map_inl]
    erw [hsl g]
    rfl
  have check := (lookup_old A bus t g (List.ofFn a)).symm.trans ((local_eq L tt (Fin.castAdd (4*q.m) g) a).trans
    ((G).subdivisionTensor_oldVertex _ u a))
  unfold w3_liftTensor WireGraph.oldVertex
  erw [Fin.addCases_left]
  unfold w3_gateWeight
  erw [slot]
  rw [check]

include hmeta in
theorem bit_entry (hA : A.ng=ng c+ne c) (b : Fin (L).nb) (a : Fin ((G).subdivision.deg
    ((G).oldVertex (Fin.natAdd (L).ng b))) → Bool) :
    let v := (G).oldVertex (Fin.natAdd (L).ng b)
    EncodesTruncPoly (w3_precision q) (w3_len q) (ecEntry (encodePortQuery q.input v.val (List.ofFn a)))
      (w3_liftTensor G weights v a) := by
  let u := Fin.natAdd (L).ng b
  let v := (G).oldVertex u
  have check := (bit_eq L tt b a).trans ((G).subdivisionTensor_oldVertex _ u a)
  have slot : w3_incSlot L sl u = .inr (Fin.natAdd A.ng b) := by
    unfold w3_incSlot
    simp only [Equiv.trans_apply,u,finSumFinEquiv_symm_apply_natAdd]
    erw [finSumFinEquiv_symm_apply_natAdd]
    rfl
  have lift : w3_liftTensor G weights v a = (if agree (List.ofFn a) then 1 else 0) := by
    unfold w3_liftTensor WireGraph.oldVertex
    erw [Fin.addCases_left]
    unfold w3_gateWeight
    erw [slot]
    rw [check]
  dsimp only
  rw [lift,equal_word q hmeta]
  · exact ind_spec q _
  · change ¬ A.ng+4*q.m+b.val < ng c
    omega
  · change ¬ (ng c+ne c ≤ A.ng+4*q.m+b.val ∧ A.ng+4*q.m+b.val < ng c+ne c+4*q.m)
    omega

include hmeta in
theorem subdivision_entry (hA : A.ng=ng c+ne c) (e : Fin (G).nE)
    (a : Fin ((G).subdivision.deg ((G).equalityVertex e)) → Bool) :
    let v := (G).equalityVertex e
    EncodesTruncPoly (w3_precision q) (w3_len q) (ecEntry (encodePortQuery q.input v.val (List.ofFn a)))
      (w3_liftTensor G weights v a) := by
  let v := (G).equalityVertex e
  have hcmp : agree (List.ofFn a) = decide (a ((G).equalityLeftPort e)=a ((G).equalityRightPort e)) := by
    exact (edge_eq G (w3_factorChecks L tt) e a).trans ((G).subdivisionTensor_equalityVertex _ e a)
  have lift : w3_liftTensor G weights v a = (if agree (List.ofFn a) then 1 else 0) := by
    unfold w3_liftTensor v WireGraph.equalityVertex
    erw [Fin.addCases_right]
    by_cases he : a ((G).equalityLeftPort e)=a ((G).equalityRightPort e)
    · have hh : agree (List.ofFn a)=true := hcmp.trans (decide_eq_true he)
      simp [he,hh]
    · have hh : agree (List.ofFn a)=false := hcmp.trans (decide_eq_false he)
      simp [he,hh]
  dsimp only
  rw [lift,equal_word q hmeta]
  · exact ind_spec q _
  · change ¬ A.ng+4*q.m+A.nb+e.val < ng c
    omega
  · change ¬ (ng c+ne c ≤ A.ng+4*q.m+A.nb+e.val ∧ A.ng+4*q.m+A.nb+e.val < ng c+ne c+4*q.m)
    omega
end

end DetDLP.M3B.ECNonlookup
end

set_option autoImplicit false
open DetDLP DetDLP.M3B DetDLP.S8H0
set_option backward.isDefEq.respectTransparency false

theorem DetDLP.nonlookupEntriesForProgram
    (q : w3_Query) (hmeta : (ECPolyDefs.dimensions q.input).2.1=q.m ∧ (ECPolyDefs.dimensions q.input).2.2.2.2.2=w3_len q) {r : ℕ} (body : NamedBlocks.B r)
    (fit : ECFits.FitsCore (ECPolyDefs.compiled q.input) body) :
    let ar := AnchoredLayout.block body.core r
    let wi := AnchoredLayout.wiring body.core body.name
    let A := S8J.CircuitRealizes.circuit ar wi
    ∀ bus : Fin (4*q.m) → Fin q.k → Fin A.nb,
      let L := ECLayout.layout A bus
      let G := w3_factorGraph L
      ∀ (sl : Fin L.ng ≃ (w3_lookupSlot q ⊕ Fin A.ng))
        (addr : (u : Fin G.nV) → (Fin (G.deg u) → Bool) → ℕ),
        (∀ g : Fin A.ng, sl (Fin.castAdd (4*q.m) g)=.inr g) →
        ∀ (v : Fin G.subdivision.nV) (a : Fin (G.subdivision.deg v) → Bool),
          (v.val < A.ng ∨ L.ng ≤ v.val) →
          EncodesTruncPoly (w3_precision q) (w3_len q)
            (ECPolyDefs.ecEntry (encodePortQuery q.input v.val (List.ofFn a)))
            (w3_liftTensor G (w3_gateWeight (q:=q) (w3_incSlot (q:=q) L sl) addr
                (w3_factorChecks L (ECLayout.test A bus (S8J.CircuitRealizes.test ar wi)))) v a) := by
  intro ar wi A bus L G sl addr hsl v a hv
  let t := S8J.CircuitRealizes.test ar wi
  let c := ECPolyDefs.compiled q.input
  have hcount : ar.A.ng = ECPolyDefs.ng c := fit.g.symm
  have hA : A.ng=ECPolyDefs.ng c+ECPolyDefs.ne c := congrArg₂ (·+·) fit.g.symm fit.e.symm
  induction v using Fin.addCases with
  | right e => exact ECNonlookup.subdivision_entry q hmeta A bus t sl addr hA e a
  | left u =>
    induction u using Fin.addCases with
    | right b => exact ECNonlookup.bit_entry q hmeta A bus t sl addr hA b a
    | left g =>
      induction g using Fin.addCases with
      | right s =>
        change A.ng+s.val < A.ng ∨ A.ng+4*q.m ≤ A.ng+s.val at hv
        have hs := s.isLt
        omega
      | left g =>
        have hw := ECNonlookup.old_weight q A bus t sl addr hsl g a
        have len := ECNonlookup.inner_length q A bus g a
        dsimp only at hw
        erw [hw]
        induction g using Fin.addCases with
        | left i =>
          have he : (List.ofFn a).length=(ECNonlookupPorts.gateEdges ar.A i).length := by
            erw [ECNonlookupPorts.cycle_edges,List.length_map] at len
            exact len
          have hcheck := (ECNonlookupPorts.fit_check fit i (List.ofFn a) he).trans
            (ECNonlookupPorts.cycle_local ar wi i (List.ofFn a)).symm
          change EncodesTruncPoly _ _ (ECPolyDefs.ecEntry (encodePortQuery q.input i.val (List.ofFn a))) _
          have hi : i.val < ECPolyDefs.ng c := fit.g.symm ▸ i.isLt
          exact ECNonlookup.ind_transport q (ECNonlookup.arith_word q hmeta i.val (List.ofFn a) hi) hcheck
        | right i =>
          have hi : i.val < ECPolyDefs.ne c := fit.e.symm ▸ i.isLt
          have low : ¬ ar.A.ng+i.val < ECPolyDefs.ng c := by rw [hcount]; omega
          have mid : ¬ (ECPolyDefs.ng c+ECPolyDefs.ne c ≤ ar.A.ng+i.val ∧
              ar.A.ng+i.val < ECPolyDefs.ng c+ECPolyDefs.ne c+4*q.m) := by rw [hcount]; omega
          change EncodesTruncPoly _ _ (ECPolyDefs.ecEntry (encodePortQuery q.input (ar.A.ng+i.val) (List.ofFn a))) _
          exact ECNonlookup.ind_transport q (ECNonlookup.equal_word q hmeta _ _ low mid)
            (ECNonlookupPorts.copy_agree ar wi i (List.ofFn a) len)



end

section
set_option autoImplicit false
set_option maxHeartbeats 400000
open DetDLP DetDLP.S8H0 DetDLP.M3B S8J S8H S8J.CircuitRealizes RegisterMap NamedBlocks ECPhysicalNet ECCert

namespace DetDLP.M3B.DegreeInputs
private theorem fiberBound {n k : ℕ} (f : Fin n → Fin k) (i : Fin k) (m : ℕ) (g : Fin n → Fin m)
    (inj : ∀ a b, f a = i → f b = i → g a = g b → a = b) : degreeOf f i ≤ m := by
  let F := (List.finRange n).filter fun e => decide (f e = i)
  have nd : F.Nodup := (List.nodup_finRange n).filter _
  have h : Function.Injective (fun x : ↥F.toFinset => g x.val) := by
    intro a b he; apply Subtype.ext; apply inj _ _ (by simpa [F] using a.property) (by simpa [F] using b.property) he
  have hh := Fintype.card_le_of_injective _ h
  rw [Fintype.card_coe,List.toFinset_card_of_nodup nd,Fintype.card_fin] at hh; exact hh

private noncomputable abbrev cap (p : ℕ) := max 12 (Nat.ceil (136*((bitLen p:ℝ)+2)^((3:ℝ)/4)))
private theorem small (p n : ℕ) (h : n ≤ 12) : n ≤ cap p := h.trans (le_max_left ..)
private theorem anchors_ok (n D : ℕ) (hd : 1 ≤ D) :
    ∀ i, degreeOf (AnchoredLayout.anchors n).gate i ≤ D := by
  intro i
  apply (fiberBound _ i 1 (fun _ => 0) (fun _ _ h k _ => h.trans k.symm)).trans hd

section
variable {p m k : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (seed : ECSeed p m) (T : ℕ) (P : Point E) (pre : List Bool)
private noncomputable abbrev ar := AnchoredLayout.block (body (k:=k) E seed T P pre).core ((ShapeOf p m k).size+1)
private noncomputable abbrev wiring := AnchoredLayout.wiring (body (k:=k) E seed T P pre).core (body (k:=k) E seed T P pre).name
private noncomputable abbrev inner := circuit (ar (k:=k) E seed T P pre) (wiring E seed T P pre)
private noncomputable abbrev bus (i : Fin (4*m)) (j : Fin k) : Fin (inner (k:=k) E seed T P pre).nb :=
  (wiring E seed T P pre).rep (busAddr i 1 (Fin.castLE (le_max_right _ _) j)).index.castSucc
end

private theorem ranges (n m : ℕ) : List.finRange (n+m) =
    (List.finRange n).map (Fin.castAdd m) ++ (List.finRange m).map (Fin.natAdd n) := by
  apply List.ext_getElem <;> simp
  case h =>
    intro i hi; by_cases h : i < n
    · rw [List.getElem_append_left (by simpa using h)]; simp
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt h)]; apply Fin.ext; simp; omega

private theorem appendedBit (A : w3_FactorLayout) {n k : ℕ} (u : Fin n → Fin k → Fin A.nb)
    (h : Function.Injective (fun e : Fin (n*k) => u (ECLayout.row e) (ECLayout.column e))) (b : Fin A.nb) :
    (w3_factorGraph (ECLayout.layout A u)).deg (Fin.natAdd _ b) ≤ (w3_factorGraph A).deg (Fin.natAdd _ b)+1 := by
  let f := fun e : Fin (n*k) => u (ECLayout.row e) (ECLayout.column e)
  let l := (List.finRange (n*k)).filter (fun e => decide (f e = b))
  have nd : l.Nodup := (List.nodup_finRange _).filter _
  have ss : Subsingleton ↥l.toFinset := ⟨fun a c => Subtype.ext (h (((show f a.val = b by simpa [l] using a.property)).trans (show f c.val = b by simpa [l] using c.property).symm))⟩
  have one : l.length ≤ 1 := by
    have hcard := Fintype.card_le_one_iff_subsingleton.mpr ss
    rw [Fintype.card_coe,List.toFinset_card_of_nodup nd] at hcard; exact hcard
  rw [w3_bitDegree (ECLayout.layout A u) b,w3_bitDegree A b]; change degreeOf (Fin.addCases A.bit f) b ≤ degreeOf A.bit b + 1
  simp only [degreeOf,ranges A.ne (n*k),List.filter_append,List.filter_map,Function.comp_def,Fin.addCases_left,Fin.addCases_right,List.length_append,List.length_map]; exact Nat.add_le_add_left one _

private theorem lowInj {p m k : ℕ} {E : WeierstrassCurve (ZMod p)} [Fact p.Prime] [E.IsElliptic] (seed : ECSeed p m) (T : ℕ) (P : Point E) (pre : List Bool) :
    Function.Injective (fun e : Fin (4*m*k) => bus E seed T P pre (ECLayout.row e) (ECLayout.column e)) := by
  intro a b he
  have hr := Fin.castAdd_injective _ _ he
  have hi := Fin.castSucc_injective _ hr
  have hp := Fin.castAdd_injective _ _ hi
  have pair := finProdFinEquiv.injective hp
  have hrow := congrArg Prod.fst pair
  apply finProdFinEquiv.symm.injective; apply Prod.ext
  · exact hrow
  have hj := congrArg Prod.snd pair
  have hh := Fin.natAdd_injective _ _ hj
  have hh := Fin.natAdd_injective _ _ hh
  have hh := Fin.natAdd_injective _ _ hh
  have hp2 := finProdFinEquiv.injective hh
  exact Fin.ext (congrArg (fun x => x.2.val) hp2)

private theorem physicalBound {p m k : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (seed : ECSeed p m) (T : ℕ) (P : Point E) (pre : List Bool) (hbody : ∀ j, degreeOf (body (k:=k) E seed T P pre).core.A.gate j ≤ cap p)
    (v : Fin (w3_factorGraph (layout (k:=k) E seed T P pre)).nV) (hv : v.val + 4*m < (layout (k:=k) E seed T P pre).ng ∨ (layout (k:=k) E seed T P pre).ng ≤ v.val) :
    (w3_factorGraph (layout (k:=k) E seed T P pre)).deg v ≤ cap p := by
  let b := (body (k:=k) E seed T P pre).core
  let f := (body (k:=k) E seed T P pre).name
  let K := (ShapeOf p m k).size+1
  let A := inner (k:=k) E seed T P pre
  let u := bus (k:=k) E seed T P pre
  induction v using Fin.addCases with
  | left g =>
    induction g using Fin.addCases with
    | left g =>
      apply (ECLayout.ordinary_degree A u g).le.trans
      induction g using Fin.addCases with
      | left g =>
        apply (NamedWires.oldDegree (AnchoredLayout.signal b f) (AnchoredLayout.block b K).A.gate g).le.trans
        induction g using Fin.addCases with
        | left i => exact (degree_left (AnchoredLayout.anchors K).gate b.A.gate i).le.trans (anchors_ok K _ (small p 1 (by decide)) i)
        | right i => exact (degree_right (AnchoredLayout.anchors K).gate b.A.gate i).le.trans (hbody i)
      | right i => exact (NamedWires.eqDegree (AnchoredLayout.signal b f) (AnchoredLayout.block b K).A.gate i).le.trans (small p _ (by decide))
    | right i =>
      change ((A.ng + i.val) + 4*m < A.ng + 4*m ∨ A.ng + 4*m ≤ A.ng + i.val) at hv
      have := i.isLt; omega
  | right i =>
    apply (appendedBit A u (lowInj seed T P pre) i).trans
    change (w3_factorGraph (CopyCycle.layout _ _)).deg (Fin.natAdd _ i)+1 ≤ _
    exact (Nat.add_le_add_right (CopyCycle.bitDegree (ar (k:=k) E seed T P pre).A.gate (wiring E seed T P pre).next i).le 1).trans (small p 4 (by decide))

private theorem cap_bound (p : ℕ) (hb : 2 ≤ bitLen p) : cap p ≤ 100000000*⌈((bitLen p:ℝ)^((3:ℝ)/4))⌉₊ := by
  let b : ℝ := bitLen p
  have b2 : 2 ≤ b := by dsimp [b]; exact_mod_cast hb
  have b0 : 0 ≤ b := by linarith
  have e0 : 0 ≤ b^((3:ℝ)/4) := Real.rpow_nonneg b0 _
  have e1 : 1 ≤ b^((3:ℝ)/4) := Real.one_le_rpow (by linarith) (by norm_num)
  have hh := Nat.le_ceil (b^((3:ℝ)/4))
  have c1 : 1 ≤ ⌈b^((3:ℝ)/4)⌉₊ := by exact_mod_cast e1.trans hh
  apply max_le (by change 12 ≤ 100000000*⌈b^((3:ℝ)/4)⌉₊; omega)
  apply Nat.ceil_le.mpr
  have h := Real.rpow_le_rpow (by linarith : 0 ≤ b+2) (by linarith : b+2 ≤ 2*b) (by norm_num : (0:ℝ) ≤ 3/4)
  rw [Real.mul_rpow (by norm_num) b0] at h
  have pow2 : (2:ℝ)^((3:ℝ)/4) ≤ 2 := by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (3:ℝ)/4 ≤ 1)
  change 136*(b+2)^((3:ℝ)/4) ≤ _; push_cast; nlinarith [mul_le_mul_of_nonneg_right pow2 e0]



end DetDLP.M3B.DegreeInputs

open DetDLP.M3B.DegreeInputs
private theorem ecPhysicalDegreeBound {p m k : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (seed : ECSeed p m) (T : ℕ) (P : Point E) (pre : List Bool) (hb : 2 ≤ bitLen p)
    (v : Fin (w3_factorGraph (layout (k:=k) E seed T P pre)).nV)
    (hv : v.val + 4*m < (layout (k:=k) E seed T P pre).ng ∨ (layout (k:=k) E seed T P pre).ng ≤ v.val) :
    (w3_factorGraph (layout (k:=k) E seed T P pre)).deg v ≤
      100000000*⌈((bitLen p:ℝ)^((3:ℝ)/4))⌉₊ := by
  exact (physicalBound E seed T P pre (m3b_ec_body_degree E seed T P pre) v hv).trans (cap_bound p hb)

end


section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option linter.unusedVariables false
open DetDLP DetDLP.M3B S8H0 ECPhysicalNet OAI.Algorithms.SubexponentialSAT S8H.WirePacket

private theorem mask {q : w3_Query} (A : w3_FactorLayout) {n k : ℕ} (bus : Fin n → Fin k → Fin A.nb)
    (num : Fin n ≃ w3_lookupSlot q) (v : Fin (w3_factorGraph (ECLayout.layout A bus)).subdivision.nV) :
    v ∈ (w3_incLookups (ECLayout.layout A bus) (ECLayout.gateSlots A bus num)).image (w3_factorGraph _).oldVertex ↔
      A.ng ≤ v.val ∧ v.val < A.ng+n := by
  let f := fun t : w3_lookupSlot q => Fin.castAdd A.nb ((ECLayout.gateSlots A bus num).symm (.inl t))
  have valf (t) : (f t).val = A.ng+(num.symm t).val := by
    change (finSumFinEquiv (.inr (num.symm t)) : Fin (A.ng+n)).val = _
    rw [finSumFinEquiv_apply_right]; rfl
  constructor
  · rintro hv; obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hu
    change A.ng ≤ (f t).val ∧ (f t).val < A.ng+n
    rw [valf]; have := (num.symm t).isLt; omega
  · rintro ⟨lo,hi⟩; let i : Fin n := ⟨v.val-A.ng,by omega⟩
    apply Finset.mem_image.mpr; refine ⟨f (num i), Finset.mem_image.mpr ⟨num i,Finset.mem_univ _,rfl⟩,?_⟩
    apply Fin.ext; change (f (num i)).val = v.val; rw [valf,num.symm_apply_apply]; dsimp [i]; omega

open ECPolyDefs OAI.Algorithms.SubexponentialSAT.SqrtLogSpace in
private def fieldsPack (w : List Bool) (a : ECPolyDefs.N) (b m k prec len : ℕ) : List Bool :=
  let d := b+1
  let e := S8H.PointAddresses.wires d
  let n := ne a; let g := ng a; let lookup := g+n; let nG := lookup+4*m; let nV := nG+n; let nE := 3*n+4*m*k
  let src := fun i => if i<n then gate a i else if i<3*n then g+(i-n)%n else lookup+(i-3*n)/k
  let dst := fun i => nG+(if i<n then i else if i<2*n then i-n else if i<3*n then succWire a (i-2*n) else
    busOff d e (max d k) ((i-3*n)/k) 1 + (i-3*n)%k)
  Encoding.encodeList id [w,S8H.WirePacket.packet nV nE src dst,countWord b,countWord m,countWord k,countWord (100000000*m*b),
    countWord prec,countWord len,(List.range (nV+nE)).map (fun j => decide (lookup ≤ j ∧ j<nG))]

private theorem transport (q : w3_Query) (hq : w3_ecQueries q) (p m k : ℕ) (hb : q.b = bitLen p) (hm : q.m = m) (hk : q.k = k)
    (A : w3_FactorLayout) (bus : Fin (4*m) → Fin k → Fin A.nb) (num : Fin (4*m) ≃ w3_lookupSlot q) :
    let L := ECLayout.layout A bus
    let G := w3_factorGraph L
  let a := ECPolyDefs.compiled q.input
  let n := ECPolyDefs.ne a
  let g := ECPolyDefs.ng a
  let ng := g+n+4*m
  let ne := 3*n+4*m*k
  let src := fun i => if i<n then ECPolyDefs.gate a i else if i<3*n then g+(i-n)%n else g+n+(i-3*n)/k
  let dst := fun i => if i<n then i else if i<2*n then i-n else if i<3*n then ECPolyDefs.succWire a (i-2*n) else ECPolyDefs.busOff (GateSemantics.d p) (GateSemantics.e p) (max (GateSemantics.d p) k) ((i-3*n)/k) 1 + (i-3*n)%k
  L.ng = ng → L.nb = n → L.ne = ne → (∀ i : Fin L.ne, (L.gate i).val = src i.val ∧ (L.bit i).val = dst i.val) →
    ECPolyDefs.ecBuild q.input = encodeTerminalBTNInstance q.input G.subdivision q.b q.m q.k (100000000*q.m*q.b)
      (w3_precision q) (w3_len q) ((w3_incLookups L (ECLayout.gateSlots A bus num)).image G.oldVertex) := by
  intro L G a n g ng ne src dst hng hnb hne hend
  have hv : ng+n=G.nV := congrArg₂ (·+·) hng.symm hnb.symm
  have he : ne=G.nE := hne.symm
  have graph : packet (ng+n) ne src (fun i => ng + dst i) = G.subdivision.encode := by
    rw [hv,he]; apply packet_eq
    · intro i; exact (hend i).1.symm
    · intro i; exact congrArg₂ (·+·) hng.symm (hend i).2.symm
  have inner : g+n=A.ng := (Nat.add_right_cancel (show A.ng+4*m=g+n+4*m from hng)).symm
  have maskEq : (List.range ((ng+n)+ne)).map (fun j => decide (g+n ≤ j ∧ j<ng)) =
      List.ofFn (fun v : Fin G.subdivision.nV => decide (v ∈ (w3_incLookups L (ECLayout.gateSlots A bus num)).image G.oldVertex)) := by
    rw [show ng+n+ne=G.subdivision.nV from congrArg₂ (·+·) hv he,List.ofFn_eq_map,
      show List.range G.subdivision.nV = (List.finRange G.subdivision.nV).map Fin.val by simp,List.map_map]
    apply List.map_congr_left; intro v _; apply Bool.eq_iff_iff.mpr
    simpa only [Function.comp_apply,decide_eq_true_eq,ng,inner] using (mask A bus num v).symm
  obtain ⟨db,dm,dk,dp,dl⟩ := m3b_ec_decoded_dimensions q hq
  let t := ECPolyDefs.dimensions q.input
  change fieldsPack q.input a t.1 t.2.1 t.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 = _
  change t.1 = q.b at db; change t.2.1 = q.m at dm; change t.2.2.1 = q.k at dk
  change t.2.2.2.2.1 = _ at dp; change t.2.2.2.2.2 = _ at dl
  simp only [db,dm,dk,dp,dl,hb,hm,hk]
  unfold fieldsPack encodeTerminalBTNInstance
  dsimp only
  have ew : S8H.PointAddresses.wires (bitLen p+1) = GateSemantics.e p := S8H.PointAddresses.wires_eq (GateSemantics.hd p)
  rw [ew]
  exact congrArg (fun z : List Bool × List Bool => Encoding.encodeList id [q.input,z.1,SqrtLogSpace.countWord (bitLen p),SqrtLogSpace.countWord m,SqrtLogSpace.countWord k,SqrtLogSpace.countWord (100000000*m*bitLen p),SqrtLogSpace.countWord (w3_precision q),SqrtLogSpace.countWord (w3_len q),z.2]) (congrArg₂ Prod.mk graph maskEq)

theorem DetDLP.M3B.packetFromLayout (q : w3_Query) (hq : w3_ecQueries q)
    {p m k T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (seed : ECSeed p m)
    (P : E.toAffine.Point) (pre : List Bool) (hb : q.b = bitLen p) (hm : q.m = m) (hk : q.k = k)
    (fit : ECFits.FitsCore (ECPolyDefs.compiled q.input) (body (k:=k) E seed T P pre))
    (num : Fin (4*m) ≃ w3_lookupSlot q) :
    let B := body (k:=k) E seed T P pre
    let A := S8J.CircuitRealizes.circuit (AnchoredLayout.block B.core ((ShapeOf p m k).size+1)) (AnchoredLayout.wiring B.core B.name)
    let bus := fun (i : Fin (4*m)) (j : Fin k) => (AnchoredLayout.wiring B.core B.name).rep (busAddr (p:=p) (k:=k) i 1 (Fin.castLE (le_max_right _ _) j)).index.castSucc
    let L := ECLayout.layout A bus
    let G := w3_factorGraph L
    ECPolyDefs.ecBuild q.input = encodeTerminalBTNInstance q.input G.subdivision q.b q.m q.k (100000000*q.m*q.b)
      (w3_precision q) (w3_len q) ((w3_incLookups L (ECLayout.gateSlots A bus num)).image G.oldVertex) := by
  intro B A bus L G
  obtain ⟨hg,hn,he,h⟩ := m3b_ec_top_layout_models E seed P pre _ fit
  exact transport q hq p m k hb hm hk A bus num hg hn he h
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
namespace DetDLP.M3B.ECWitCore
open S8J S8J.CircuitRealizes S8H0 RegisterMap NamedBlocks
open ECCert ECPhysicalNet
section
variable {m : ℕ}
/-- Slot order in the physical layout alternates sides within each factor pair. -/
def slotNumber : (Fin m × Fin 2 × Bool) ≃ Fin (4*m) where
  toFun t := ix t.2.2 (pointIdx t.1 t.2.1)
  invFun i := (⟨i.val/4,by omega⟩, ⟨i.val/2%2,by omega⟩, decide (i.val%2=1))
  left_inv := by
    rintro ⟨b,j,s⟩; cases s <;> apply Prod.ext <;> first | apply Prod.ext | skip
    all_goals first | apply Fin.ext | skip
    all_goals simp [ix,pointIdx] <;> omega
  right_inv i := Fin.ext (by
    change 2*(2*(i.val/4)+(i.val/2%2)) + (decide (i.val%2=1)).toNat = i.val
    by_cases h : i.val%2=1 <;> simp [h] <;> omega)
end
variable {p m k : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (seed : ECSeed p m) (T : ℕ) (P : Point E) (pre : List Bool)
noncomputable abbrev ar := AnchoredLayout.block (body (k:=k) E seed T P pre).core ((ShapeOf p m k).size+1)
noncomputable abbrev wiring := AnchoredLayout.wiring (body (k:=k) E seed T P pre).core (body (k:=k) E seed T P pre).name
noncomputable abbrev inner := circuit (ar (k:=k) E seed T P pre) (wiring E seed T P pre)
noncomputable abbrev bus (i : Fin (4*m)) (j : Fin k) : Fin (inner (k:=k) E seed T P pre).nb :=
  (wiring E seed T P pre).rep (busAddr i 1 (Fin.castLE (le_max_right _ _) j)).index.castSucc
noncomputable abbrev vertex := ECLayout.vertex (inner (k:=k) E seed T P pre) (bus E seed T P pre)
noncomputable abbrev port := ECLayout.port (inner (k:=k) E seed T P pre) (bus E seed T P pre)
noncomputable def readAddress (i : Fin (4*m))
    (values : Fin ((w3_factorGraph (layout (k:=k) E seed T P pre)).deg (vertex E seed T P pre i)) → Bool) :=
  bitsToNat (fun j : Fin k => values (port E seed T P pre i j))

variable (F : Fin m → List (Point E)) (hT : T ≤ p) (hk : 2*T ≤ 2^k) (hF : ListsOK E F seed T) (hp : 3 < p) (hm : 1 ≤ m)

private noncomputable abbrev geometryEquiv :=
  (physicalAddressEquivForProgram (k := k) E seed T P pre F hT hk hF hp hm).choose

/-- Read the significance-ordered address bits at the actual lookup vertex.
    The edge assignment, not a named-register environment, supplies these bits. -/
theorem local_address (a : {x // (w3_factorGraph (layout (k:=k) E seed T P pre)).Satisfies (w3_factorChecks _ (test E seed T P pre)) x})
    (b : Fin m) (j : Fin 2) (s : Bool) :
    let i := ix s (pointIdx b j)
    let x := w3_factorEquiv _ _ a
    let t := (geometryEquiv E seed T P pre F hT hk hF hp hm x).val
    readAddress E seed T P pre i (w3_wireLocal _ (vertex E seed T P pre i) a.val) =
      ECAddress.address E seed T b ((F b).get (if s then t.2 b j else t.1 b j)) := by
  apply Eq.trans _ ((physicalAddressEquivForProgram E seed T P pre F hT hk hF hp hm).choose_spec.2
    (w3_factorEquiv _ _ a) b j s)
  apply congrArg bitsToNat; funext l
  exact ECLayout.read_accepted (inner (k:=k) E seed T P pre) (bus E seed T P pre)
    (CircuitRealizes.test (ar E seed T P pre) (wiring E seed T P pre)) a _ l


private theorem vertex_inj : Function.Injective (vertex (k:=k) E seed T P pre) := by
  intro i j he
  have h := congrArg Fin.val he
  change (inner (k:=k) E seed T P pre).ng + i.val = (inner (k:=k) E seed T P pre).ng + j.val at h
  exact Fin.ext (Nat.add_left_cancel h)

noncomputable def address (v : Fin (w3_factorGraph (layout (k:=k) E seed T P pre)).nV)
    (values : Fin ((w3_factorGraph (layout (k:=k) E seed T P pre)).deg v) → Bool) : ℕ := by
  classical
  exact if h : ∃ i, vertex E seed T P pre i = v then
    readAddress E seed T P pre h.choose (h.choose_spec.symm ▸ values) else 0

theorem address_vertex (i : Fin (4*m)) (values : Fin ((w3_factorGraph (layout (k:=k) E seed T P pre)).deg (vertex E seed T P pre i)) → Bool) :
    address E seed T P pre _ values = readAddress E seed T P pre i values := by
  classical
  have h : ∃ j, vertex (k:=k) E seed T P pre j = vertex E seed T P pre i := ⟨i,rfl⟩
  unfold address; rw [dif_pos h]
  have eq := vertex_inj E seed T P pre h.choose_spec
  have aux (j : Fin (4*m)) (e : vertex (k:=k) E seed T P pre j = vertex E seed T P pre i) (hji : j = i) :
      readAddress E seed T P pre j (e.symm ▸ values) = readAddress E seed T P pre i values := by subst j; rfl
  exact aux _ h.choose_spec eq

section Query
variable {M : ℕ} [NeZero M] (y : w3_Label M (base E F).totalCoords) (input : List Bool)
noncomputable def query : w3_Query where
  V := Point E
  M := M
  nz := inferInstance
  b := bitLen p
  m := m
  k := k
  FB := base E F
  P := P
  y := y
  code := w3_tupleWord (base E F) (fun A => (pointCoords A).flatMap (w3_bits (bitLen p)))
  pre := pre
  input := input
  addr i j := ECAddress.address E seed T i ((F i).get j)

noncomputable abbrev slots := ECLayout.gateSlots (q:=query (k:=k) E seed T P pre F y input) (inner (k:=k) E seed T P pre) (bus E seed T P pre) slotNumber.symm
private theorem gate_at (u : Fin m × Fin 2 × Bool) :
    (slots (k:=k) E seed T P pre F y input).symm (.inl u) = Fin.natAdd (inner (k:=k) E seed T P pre).ng (slotNumber u) := by
  change finSumFinEquiv (.inr (slotNumber u)) = _
  exact finSumFinEquiv_apply_right ..
private theorem inc_at (u : Fin m × Fin 2 × Bool) :
    (w3_incSlot (layout (k:=k) E seed T P pre) (slots E seed T P pre F y input)).symm (.inl u) = vertex E seed T P pre (slotNumber u) := by
  change finSumFinEquiv (.inl ((slots E seed T P pre F y input).symm (.inl u))) = _
  rw [finSumFinEquiv_apply_left, gate_at]; rfl

theorem lookupDegree (u : Fin m × Fin 2 × Bool) :
    (w3_factorGraph (layout (k:=k) E seed T P pre)).deg (Fin.castAdd _ ((slots E seed T P pre F y input).symm (.inl u))) = k := by
  rw [gate_at]; exact ECLayout.lookup_degree (inner E seed T P pre) (bus E seed T P pre) _

theorem lookupAddress (a : {x // (w3_factorGraph (layout (k:=k) E seed T P pre)).Satisfies (w3_factorChecks _ (test E seed T P pre)) x})
    (b : Fin m) (j : Fin 2) (s : Bool) :
    let q := query (k:=k) E seed T P pre F y input
    let t := (geometryEquiv E seed T P pre F hT hk hF hp hm (w3_factorEquiv _ _ a)).val
    let v := (w3_incSlot (layout (k:=k) E seed T P pre) (slots E seed T P pre F y input)).symm (.inl (b,j,s))
    address E seed T P pre v (w3_wireLocal _ v a.val) = q.addr b (if s then t.2 b j else t.1 b j) := by
  let G := w3_factorGraph (layout (k:=k) E seed T P pre)
  let read := fun v : Fin G.nV => address E seed T P pre v (w3_wireLocal G v a.val)
  exact (congrArg read (inc_at (k:=k) E seed T P pre F y input (b,j,s))).trans
    ((address_vertex E seed T P pre _ _).trans (local_address E seed T P pre F hT hk hF hp hm a b j s))
/-- Incidence core with all assignment, lookup-count, port-degree, and address
    obligations discharged. Only external resource bounds and injectivity remain. -/
noncomputable def coreOfBounds {C S : ℕ} (hp : 3 < p) (hm : 1 ≤ m)
    (hi : ∀ i, Function.Injective ((query (k:=k) E seed T P pre F y input).addr i))
    (he : 2*(layout (k:=k) E seed T P pre).ne ≤ S)
    (hd : ∀ v ∉ w3_incLookups (layout (k:=k) E seed T P pre) (slots E seed T P pre F y input),
      (w3_factorGraph (layout (k:=k) E seed T P pre)).deg v ≤ C * Nat.ceil (((bitLen p : ℕ):ℝ)^((3:ℝ)/4)))
    (heq : 2 ≤ C * Nat.ceil (((bitLen p : ℕ):ℝ)^((3:ℝ)/4)))
    (shape : let q := query (k:=k) E seed T P pre F y input
      2 ≤ q.b ∧ 1 ≤ q.m ∧ 1 ≤ q.k ∧ blockCount q.b ≤ C*q.m ∧ q.m ≤ C*blockCount q.b ∧
      S ≤ C*q.m*q.b ∧ 4*q.m*q.k ≤ C*q.b ∧ q.b ≤ C*(4*q.m*q.k) ∧
      1 ≤ w3_precision q ∧ w3_precision q ≤ S ∧ 1 ≤ w3_len q ∧ w3_len q ≤ C*q.m) :
    w3_WireCore (query (k:=k) E seed T P pre F y input) C :=
  w3_incCore (layout E seed T P pre) (slots E seed T P pre F y input) (test E seed T P pre)
    (geometryEquiv E seed T P pre F hT hk hF hp hm) (address E seed T P pre) hi
    (lookupAddress E seed T P pre F hT hk hF hp hm y input) (lookupDegree E seed T P pre F y input) he hd heq shape
end Query

end DetDLP.M3B.ECWitCore
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace DetDLP.M3B.ECWitGeom
end DetDLP.M3B.ECWitGeom
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.M3B.ECWitness
open Groundwork w4_M5Network OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
private theorem native_frameLength (w : List Bool) : (Encoding.frame w).length = 2*w.length+1 := by
  induction w with
  | nil => rfl
  | cons b w ih => change (Encoding.frame w).length+1+1 = 2*(w.length+1)+1; omega

private theorem native_encodedMemberLength {α : Type*} {enc : α → List Bool} {a : α} {xs : List α}
    (ha : a ∈ xs) : (enc a).length + 1 ≤ (Encoding.encodeList enc xs).length := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [Encoding.encodeList,List.length_cons,List.length_append,native_frameLength]
    rcases List.mem_cons.mp ha with rfl | h
    · omega
    · have := ih h; omega

private theorem native_queryExactLength (w a : List Bool) (v : ℕ) :
    (encodePortQuery w v a).length = 2*(w.length+(countWord v).length+a.length)+7 := by
  simp [encodePortQuery, Encoding.encodeList,native_frameLength]; omega

private theorem native_queryIndexLength (n : ℕ) : (countWord n).length ≤ n+1 := by
  by_cases h : n = 0
  · simp [h,countWord]
  · simp only [countWord,if_neg h,Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr n.lt_two_pow_self).trans (Nat.le_succ _)

theorem packet_vertices {q : w3_Query} {C : ℕ} (W : w3_WireCore q C) :
    W.G.subdivision.nV ≤ (w3_wirePacket W).length := by
  let g := W.G.subdivision
  let mask := List.ofFn (fun v : Fin g.nV => decide (v ∈ W.L.image W.G.oldVertex))
  let fields := [W.desc,g.encode,countWord q.b,countWord q.m,countWord q.k,countWord W.S,
    countWord (w3_precision q),countWord (w3_len q),mask]
  have h := native_encodedMemberLength (enc:=id) (show mask ∈ fields by simp [fields])
  change mask.length+1 ≤ (w3_wirePacket W).length at h
  simpa [mask,g] using Nat.le_of_succ_le h

theorem wire_bounds (build : List Bool → List Bool) (poly : PolyT build) :
    ∃ c : ℕ, 0<c ∧ ∀ {q : w3_Query} {C : ℕ} (W : w3_WireCore q C),
      build W.desc = w3_wirePacket W →
      W.G.subdivision.nV ≤ (W.S+W.desc.length+1)^c ∧
      ∀ (v : Fin W.G.subdivision.nV) (a : Fin (W.G.subdivision.deg v) → Bool),
        (encodePortQuery W.desc v.val (List.ofFn a)).length+1 ≤ (W.S+W.desc.length+1)^c := by
  obtain ⟨f,⟨c,hc⟩,_,hf⟩ := PolyT.len_bound poly
  refine ⟨4*c+5,by omega,?_⟩
  intro q C W hW
  let B := W.S+W.desc.length+1
  have hs : 1 ≤ W.S := W.shape.2.2.2.2.2.2.2.2.1.trans W.shape.2.2.2.2.2.2.2.2.2.1
  have hB : 2≤B := by dsimp [B];omega
  have hb1 : 1≤B := by omega
  have h4 : 4 ≤ B^2 := Nat.pow_le_pow_left hB 2
  have hsmall : 3*W.desc.length+2+1 ≤ B^3 := by
    rw [show (3:ℕ)=2+1 by decide,pow_succ]
    exact (show 3*W.desc.length+2+1 ≤ 4*B by dsimp [B];omega).trans (Nat.mul_le_mul_right B h4)
  have hcoef : c≤B^c := (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_left hB c)
  have hnum := (hf W.desc).trans (hc (Groundwork.len W.desc))
  rw [Groundwork.len_bools,Groundwork.len_bools] at hnum
  have hv0 := packet_vertices W
  rw [←hW] at hv0
  have hv : W.G.subdivision.nV ≤ B^(4*c) := by
    calc
      _ ≤ c*(3*W.desc.length+2+1)^c := by omega
      _ ≤ B^c*(B^3)^c := Nat.mul_le_mul hcoef (Nat.pow_le_pow_left hsmall c)
      _ = B^(4*c) := by rw [← pow_mul,← pow_add]; congr 1;omega
  let N := B^(4*c+1)
  have hV : W.G.subdivision.nV ≤ N := hv.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hBN : B≤N := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (by omega : 0<B) (show 1≤4*c+1 by omega))
  have pow : 16*N ≤ B^(4*c+5) := by
    rw [show 4*c+5=4+(4*c+1) by omega,pow_add]
    exact Nat.mul_le_mul_right _ (show 2^4≤B^4 from Nat.pow_le_pow_left hB 4)
  constructor
  · exact hV.trans ((show N ≤ 16*N by omega).trans pow)
  · intro v a
    have hvi : v.val<W.G.subdivision.nV := v.isLt
    have hcount := native_queryIndexLength v.val
    have hdeg : W.G.subdivision.deg v ≤ W.G.subdivision.nE := (List.length_filter_le ..).trans List.length_finRange.le
    rw [WireGraph.subdivision_nE] at hdeg
    have hed := W.core_edges
    rw [native_queryExactLength,List.length_ofFn]
    apply le_trans _ pow
    change 2*(W.desc.length+(countWord v.val).length+W.G.subdivision.deg v)+7+1≤16*N
    have hsum : W.desc.length+W.S+1 ≤ N := by dsimp [B] at hBN;omega
    omega

end DetDLP.M3B.ECWitness
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace DetDLP.M3B.ECWitness
open ECPolyDefs Groundwork w4_M5Network S8J
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [-simp] Fin.natAdd_eq_addNat

def ind (n : ℕ) (b : Bool) := encodeNatListBin ((List.range n).map (fun j => if b && j=0 then 1 else 0))
def bin (n P : ℕ) (z : ℤ) := encodeNatListBin ((List.range n).map (fun j => (Ring.choose z j % (2^P:ℤ)).toNat))

private theorem indicator_spec (P n : ℕ) (hp : 0 < P) (hn : 0 < n) (b : Bool) :
    EncodesTruncPoly P n (ind n b) (if b then 1 else 0) := by
  classical
  let c (i : Fin n) := if i.val = 0 then b.toNat else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · have h : 1 < 2^P := Nat.one_lt_pow (by omega) (by decide)
    intro i; cases b <;> simp [c] <;> split <;> omega
  · unfold ind
    congr 1
    rw [List.ofFn_eq_map, show List.range n = (List.finRange n).map Fin.val by simp, List.map_map]
    apply List.map_congr_left
    intro i _
    cases b <;> simp [c,Function.comp_def]
  · cases b with
    | false => simp [truncPolyOfCoeffs,c]
    | true =>
      let z : Fin n := ⟨0,hn⟩
      unfold truncPolyOfCoeffs
      rw [Finset.sum_eq_single z]
      · simp [z,c,Polynomial.monomial_zero_left]
      · intro i _ h; have hi : i.val ≠ 0 := fun e => h (Fin.ext e); simp [c,hi]
      · simp



theorem bin_spec (q : w3_Query) (z : ℤ) : EncodesTruncPoly (w3_precision q) (w3_len q)
    (bin (w3_len q) (w3_precision q) z) (w3_binWord q z) := by
  let P := w3_precision q
  let c (i : Fin (w3_len q)) := (Ring.choose z i.val % (2^P:ℤ)).toNat
  have pos : 0 < (2:ℤ)^P := by positivity
  refine ⟨c,?_,?_,?_⟩
  · intro j
    have he := Int.emod_lt_of_pos (Ring.choose z j.val) pos
    have hn := Int.emod_nonneg (Ring.choose z j.val) pos.ne'
    exact_mod_cast (show (((Ring.choose z j.val % (2:ℤ)^P).toNat:ℕ):ℤ) < (2:ℤ)^P by simpa only [Int.toNat_of_nonneg hn] using he)
  · unfold bin
    congr 1
    rw [List.ofFn_eq_map,show List.range (w3_len q)=(List.finRange (w3_len q)).map Fin.val by simp,List.map_map]
    rfl
  · unfold w3_binWord truncPolyOfCoeffs; congr 1
    apply Finset.sum_congr rfl; intro i _; congr 1
    change ((intBinom z i.val : ℤ) : ZMod (2^P)) = (((intBinom z i.val % ((2:ℤ)^P)).toNat : ℕ) : ZMod (2^P))
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ pos.ne')]
    change _ = ((intBinom z i.val % ((2^P : ℕ):ℤ) : ℤ) : ZMod (2^P)); exact (ZMod.intCast_mod _ _).symm



theorem num_lookup (q : w3_Query) (hq : w3_ecQueries q) (s : Fin (4*q.m)) (i : Fin q.m)
    (hi : s.val/4=i.val) (bs : W) :
    let start := ng (compiled q.input)+ne (compiled q.input)
    EncodesTruncPoly (w3_precision q) (w3_len q)
      (ecEntry (encodePortQuery q.input (start+s.val) bs))
      (w3_addressWeight q i (decide (s.val%2=1)) (PolyT.bval bs)) := by
  let c := compiled q.input
  let start := ng c+ne c
  obtain ⟨_,hm,_,hp,hn⟩ := m3b_ec_decoded_dimensions q hq
  have hl : ¬start+s.val<ng c := by dsimp [start];omega
  have hr : start ≤ start+s.val ∧ start+s.val < start+4*q.m := ⟨Nat.le_add_right ..,Nat.add_lt_add_left s.isLt _⟩
  have hx := m3b_ec_lookup_scan q hq i (PolyT.bval bs)
  let z := encodePortQuery q.input (start+s.val) bs
  have h1 : DetDLP_W1_Queries.first z=q.input := by simp [z,encodePortQuery]
  have h2 : PolyT.bval (DetDLP_W1_Queries.second z)=start+s.val := by simp [z,encodePortQuery,DetDLP_W1_Queries.second]
  have h3 : DetDLP_W1_Queries.third z=bs := by simp [z,encodePortQuery,DetDLP_W1_Queries.third,DetDLP_W1_Queries.second]
  change EncodesTruncPoly _ _ (ecEntry z) _
  simp only [ecEntry,h1,h2,h3]
  change EncodesTruncPoly _ _ (if start+s.val < ng c then _ else if start ≤ start+s.val ∧ start+s.val < start+4*(dimensions q.input).2.1 then _ else _) _
  rw [if_neg hl,hm,if_pos hr,Nat.add_sub_cancel_left,hi,hx,hp,hn]
  unfold w3_addressWeight
  cases h : w3_lookupIndex q i (PolyT.bval bs) with
  | none =>
    exact indicator_spec (w3_precision q) (w3_len q) (by unfold w3_precision;omega) (by unfold w3_len;omega) false
  | some r =>
    simpa only [Option.map_some,decide_eq_true_eq,bin] using
      bin_spec q (if s.val%2=1 then ((q.y (q.FB.coordOf i r)).val:ℤ) else -((q.y (q.FB.coordOf i r)).val:ℤ))

end DetDLP.M3B.ECWitness
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace DetDLP.M3B.ECWitness
open S8J Groundwork ECPolyDefs w4_M5Network
attribute [-simp] Fin.natAdd_eq_addNat
private theorem bval_ofFn_bitsToNat {d : ℕ} (a : Fin d → Bool) :
    PolyT.bval (List.ofFn a) = bitsToNat a := by
  induction d with
  | zero => simp [PolyT.bval, bitsToNat]
  | succ d ih =>
    rw [List.ofFn_succ, PolyT.bval_cons]
    rw [bitsToNat, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    rw [ih (fun i => a i.succ)]
    simp only [← Nat.mul_assoc, ← Finset.sum_mul, bitsToNat]
    cases h : a 0 <;> simp [Nat.mul_comm, Nat.add_comm]


theorem located_lookup (q : w3_Query) (hq : w3_ecQueries q) (A : w3_FactorLayout)
    (bus : Fin (4*q.m) → Fin q.k → Fin A.nb) (t : w3_factorTest A)
    (sl : Fin (ECLayout.layout A bus).ng ≃ (w3_lookupSlot q ⊕ Fin A.ng))
    (addr : (v : Fin (w3_factorGraph (ECLayout.layout A bus)).nV) → (Fin ((w3_factorGraph _).deg v) → Bool) → ℕ)
    (hA : A.ng=ng (compiled q.input)+ne (compiled q.input))
    (s : Fin (4*q.m)) (blk : Fin q.m) (crd : Fin 2) (hblk : s.val/4=blk.val)
    (hsl : sl (Fin.natAdd A.ng s)=.inl (blk,crd,decide (s.val%2=1)))
    (haddr : ∀ values, addr (ECLayout.vertex A bus s) values = bitsToNat
      (fun j : Fin q.k => values (ECLayout.port A bus s j)))
    (a : Fin ((w3_factorGraph (ECLayout.layout A bus)).subdivision.deg
      ((w3_factorGraph (ECLayout.layout A bus)).oldVertex (ECLayout.vertex A bus s))) → Bool) :
    let G := w3_factorGraph (ECLayout.layout A bus)
    let v := G.oldVertex (ECLayout.vertex A bus s)
    EncodesTruncPoly (w3_precision q) (w3_len q) (ecEntry (encodePortQuery q.input v.val (List.ofFn a)))
      (w3_liftTensor G (w3_gateWeight (w3_incSlot (ECLayout.layout A bus) sl) addr
        (w3_factorChecks _ (ECLayout.test A bus t))) v a) := by
  let G := w3_factorGraph (ECLayout.layout A bus)
  let u := ECLayout.vertex A bus s
  let v := G.oldVertex u
  let localbits : Fin (G.deg u) → Bool := fun j => a (G.oldPort u j)
  have hbval : PolyT.bval (List.ofFn a) = bitsToNat (fun j : Fin q.k => localbits (M3B.ECLayout.port A bus s j)) := by
    rw [bval_ofFn_bitsToNat]
    have hd : G.subdivision.deg v = q.k := (G.subdivision_deg_oldVertex u).trans (M3B.ECLayout.lookup_degree A bus s)
    let idx (j : Fin q.k) := G.oldPort u (M3B.ECLayout.port A bus s j)
    let es := G.subdivision.ports v
    have sorted : es.Pairwise (· < ·) := (List.pairwise_lt_finRange _).filter _
    have getE (j : Fin q.k) : es.get (idx j) = G.leftHalf (M3B.ECLayout.edge A bus s j) := by
      change (G.subdivision.ports (G.oldVertex u)).get (G.oldPort u _) = _
      rw [G.get_oldPort, show (G.ports u).get (M3B.ECLayout.port A bus s j) = M3B.ECLayout.edge A bus s j from G.get_portIndex ..]
      apply if_pos
      apply congrArg (Fin.castAdd A.nb)
      simp [M3B.ECLayout.edge, M3B.ECLayout.layout, splitMap, M3B.ECLayout.row]
    have strict : StrictMono (fun j => Fin.cast hd (idx j)) := by
      intro i j hij
      change idx i < idx j
      apply (show StrictMono es.get from fun _ _ h => List.pairwise_iff_get.mp sorted _ _ h).lt_iff_lt.mp
      rw [getE, getE]
      change A.ne + (i.val + q.k * s.val) < A.ne + (j.val + q.k * s.val)
      exact Nat.add_lt_add_left (Nat.add_lt_add_right hij _) _
    have eqidx (j : Fin q.k) : idx j = Fin.cast hd.symm j := Fin.ext (congrArg (fun x : Fin q.k => x.val) (strict.apply_eq (x:=j)))
    change bitsToNat a = bitsToNat (fun j => a (idx j))
    simp_rw [eqidx]
    exact (show ∀ {b c : ℕ} (h : b = c) (f : Fin b → Bool), bitsToNat f = bitsToNat (fun j => f (Fin.cast h.symm j)) by intros b c h f; subst c; rfl) hd a
  have haddr' : addr u localbits = PolyT.bval (List.ofFn a) := by
    rw [haddr, hbval]
  have hslot : w3_incSlot (M3B.ECLayout.layout A bus) sl u = .inl (blk, crd, decide (s.val%2=1)) := by
    change (w3_incSlot (M3B.ECLayout.layout A bus) sl) (Fin.castAdd A.nb (Fin.natAdd A.ng s)) = _
    simp [w3_incSlot, Equiv.trans_apply]
    erw [finSumFinEquiv_symm_apply_castAdd]
    simp [hsl]
  have htest : w3_factorChecks (M3B.ECLayout.layout A bus) (M3B.ECLayout.test A bus t) u localbits = true := by
    unfold w3_factorChecks u M3B.ECLayout.vertex
    erw [Fin.addCases_left]
    unfold M3B.ECLayout.test
    erw [Fin.addCases_right]
  have hweight : w3_liftTensor G
      (w3_gateWeight (w3_incSlot (M3B.ECLayout.layout A bus) sl) addr
        (w3_factorChecks _ (M3B.ECLayout.test A bus t))) v a =
      w3_addressWeight q blk (decide (s.val%2=1)) (PolyT.bval (List.ofFn a)) := by
    unfold w3_liftTensor w4_M5Network.WireGraph.oldVertex
    erw [Fin.addCases_left]
    unfold w3_gateWeight
    rw [htest, if_pos rfl, hslot, haddr']

  dsimp only
  rw [hweight]
  change EncodesTruncPoly _ _ (ecEntry (encodePortQuery q.input (A.ng+s.val) (List.ofFn a))) _
  rw [hA]
  exact num_lookup q hq s blk hblk (List.ofFn a)
end DetDLP.M3B.ECWitness
end


section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace DetDLP.M3B.ECWitness
open ECWitCore ECPolyDefs ECPhysicalNet ECCert S8J S8J.CircuitRealizes S8H0
attribute [-simp] Fin.natAdd_eq_addNat
variable {p m k M : ℕ} [Fact p.Prime] [NeZero M] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (seed : ECSeed p m) (T : ℕ) (P : Point E) (η : List Bool) (F : Fin m → List (Point E))
variable (y : w3_Label M (ECCert.base E F).totalCoords) (input : List Bool)
local notation "Q" => query (k:=k) E seed T P η F y input
local notation "A" => ECWitCore.inner (k:=k) E seed T P η
local notation "B" => ECWitCore.bus (m:=m) (k:=k) E seed T P η
local notation "L" => ECPhysicalNet.layout (k:=k) E seed T P η
local notation "G" => w3_factorGraph L
local notation "arB" => ECWitCore.ar (k:=k) E seed T P η
local notation "wi" => ECWitCore.wiring (k:=k) E seed T P η
local notation "ts" => S8J.CircuitRealizes.test arB wi
local notation "sl" => slots (k:=k) E seed T P η F y input
local notation "adr" => ECWitCore.address (k:=k) E seed T P η
local notation "wt" => w3_gateWeight (w3_incSlot L sl) adr (w3_factorChecks L (ECLayout.test A B ts))
local notation "c" => compiled input

theorem native_entries (hq : w3_ecQueries Q) (fit : ECFits.FitsCore c (body (k:=k) E seed T P η))
    (v : Fin (G).subdivision.nV) (a : Fin ((G).subdivision.deg v) → Bool) :
    EncodesTruncPoly (w3_precision Q) (w3_len Q) (ecEntry (encodePortQuery input v.val (List.ofFn a)))
      (w3_liftTensor G wt v a) := by
  have hA : (A).ng=ng c+ne c := congrArg₂ (·+·) fit.g.symm fit.e.symm
  have hsl (g : Fin (A).ng) : sl (Fin.castAdd (4*m) g)=.inr g := by
    simp [ECWitCore.slots,ECLayout.gateSlots]
    erw [finSumFinEquiv_symm_apply_castAdd]
    rfl
  obtain ⟨_,hmword,_,_,hlenword⟩ := m3b_ec_decoded_dimensions Q hq
  have checked := DetDLP.nonlookupEntriesForProgram Q ⟨hmword,hlenword⟩ (body (k:=k) E seed T P η) fit B sl adr hsl
  induction v using Fin.addCases with
  | right e =>
    apply checked _ a
    right; change (L).ng ≤ (L).ng+(L).nb+e.val; omega
  | left u =>
    induction u using Fin.addCases with
    | right b =>
      apply checked _ a
      right; exact Nat.le_add_right (L).ng b.val
    | left g =>
      induction g using Fin.addCases with
      | left i => exact checked _ a (Or.inl i.isLt)
      | right s =>
        let index := (slotNumber (m:=m)).symm s
        apply located_lookup Q hq A B ts sl adr hA s index.1 index.2.1 rfl _ _ a
        · simp [ECWitCore.slots,ECLayout.gateSlots]
          erw [finSumFinEquiv_symm_apply_natAdd]
          rfl
        · exact address_vertex E seed T P η s

end DetDLP.M3B.ECWitness
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
open DetDLP DetDLP.M3B S8H0 ECPhysicalNet ECCert ECWitCore
open OAI.Algorithms.SubexponentialSAT ECPolyDefs
private theorem threshold_le_for_native {p m g : ℕ} (hm : 2 ≤ m) (h64 : 64 ≤ g) (h4096 : 4096*m ≤ g-1) :
    hashThreshold p (g-1) m g ≤ p := by
  have hn : (64:ℝ) ≤ g := by exact_mod_cast h64
  have hg : ((g-1:ℕ):ℝ) = (g:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ g)]; norm_num
  have hp : 0 < ((g-1:ℕ):ℝ) := by rw [hg]; linarith
  have he : (1:ℝ)/(m:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hm)
  have h16 : (16*(g:ℝ))^((1:ℝ)/(m:ℝ)) ≤ ((g-1:ℕ):ℝ) := by
    calc
      _ ≤ (16*(g:ℝ))^((1:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le (by linarith) he
      _ ≤ (((g-1:ℕ):ℝ)^2)^((1:ℝ)/2) := Real.rpow_le_rpow (by positivity) (by rw [hg]; nlinarith [mul_nonneg (by linarith : 0 ≤ (g:ℝ)-18) (by positivity : 0 ≤ (g:ℝ))]) (by norm_num)
      _ = _ := by rw [← Real.rpow_natCast_mul hp.le]; norm_num
  have hq : qStar m g ≤ g-1 := max_le h4096 (Nat.ceil_le.mpr h16)
  apply Nat.ceil_le.mpr
  exact (div_le_iff₀ hp).mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hq) (by positivity))

namespace DetDLP.M3B.ECWitness
def Entries : Prop :=
  ∀ {p m k M : ℕ} [Fact p.Prime] [NeZero M] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (seed : ECSeed p m) (T : ℕ) (P : Point E) (η : List Bool) (F : Fin m → List (Point E))
    (y : w3_Label M (ECCert.base E F).totalCoords) (input : List Bool),
    let q := query (k:=k) E seed T P η F y input
    let L := layout (k:=k) E seed T P η
    let G := w3_factorGraph L
    let ss := slots (k:=k) E seed T P η F y input
    let ws := w3_gateWeight (q:=q) (w3_incSlot L ss) (ECWitCore.address E seed T P η)
      (w3_factorChecks L (ECPhysicalNet.test E seed T P η))
    w3_ecQueries q → ECFits.FitsCore (compiled input) (body (k:=k) E seed T P η) →
    ∀ (v : Fin G.subdivision.nV) (a : Fin (G.subdivision.deg v) → Bool),
      EncodesTruncPoly (w3_precision q) (w3_len q) (ecEntry (encodePortQuery input v.val (List.ofFn a)))
        (w3_liftTensor G ws v a)
end DetDLP.M3B.ECWitness

theorem DetDLP.M3B.ECWitness.witness_of_entries (hen : ECWitness.Entries)
    (hcore : ∀ q, w3_ecQueries q →
      ∃ W : w3_WireCore q 100000000, W.desc = q.input ∧ W.S = 100000000 * q.m * q.b) :
    ∃ c : ℕ, 0 < c ∧
      ∀ q, w3_ecQueries q → ∃ W : w3_WireCore q 100000000,
        ecBuild q.input = w3_wirePacket W ∧
        W.G.subdivision.nV ≤ (W.S + W.desc.length + 1) ^ c ∧
        ∀ (v : Fin W.G.subdivision.nV) (a : Fin (W.G.subdivision.deg v) → Bool),
          let w := encodePortQuery W.desc v.val (List.ofFn a)
          w.length + 1 ≤ (W.S + W.desc.length + 1) ^ c ∧
          EncodesTruncPoly (w3_precision q) (w3_len q) (ecEntry w)
            (w3_liftTensor W.G W.T v a) := by
  obtain ⟨c,hc,allbounds⟩ := ECWitness.wire_bounds ecBuild m3b_ec_build_poly
  refine ⟨c,hc,?_⟩
  intro q hq
  obtain ⟨old,hdesc,hsize⟩ := hcore q hq
  have shape := old.shape
  rw [hsize] at shape
  clear hdesc hsize old
  have hq₀ := hq
  have hi := w3_native_lookup_address q (Or.inr hq)
  obtain ⟨p,ip,E,hE,h1,h2,h3,p67,g64,hNZ,hM,seed,F,hF,P,y,pre,rfl⟩ := hq
  letI := ecPointFintype E
  let g := Fintype.card E.toAffine.Point
  let b := bitLen p
  let m := blockCount b
  let T := hashThreshold p (g-1) m g
  let k := Nat.clog 2 (2*T)
  let w := Encoding.encodeList id [encodeCurveInput p E,encodeNatListBin (pointCoords P),encodeNatListBin [g,T],encodeNatListBin ((List.finRange m).flatMap fun i => [(seed i false).1.val+1,(seed i false).2.val,(seed i true).1.val+1,(seed i true).2.val]),encodeECFactorBlocks F,encodeNatListBin (List.ofFn fun j => (y j).val),pre]
  let Q := query (k:=k) E seed T P pre F y w
  have hm : 2 ≤ m := le_max_left ..
  have hbp : p ≤ 2^b := Nat.le_pow_clog (by decide) _
  have hb : 2 ≤ b := by by_contra! h; have := Nat.pow_le_pow_right (by decide : 0<2) (show b ≤ 1 by omega); omega
  have ht : T ≤ p := threshold_le_for_native hm g64 hM
  have hk' : k ≤ b+1 := Nat.clog_le_of_le_pow (by rw [pow_succ]; omega)
  have hd (v : Fin (w3_factorGraph (layout (k:=k) E seed T P pre)).nV) (hv : v ∉ w3_incLookups (layout (k:=k) E seed T P pre) (slots E seed T P pre F y w)) :
      (w3_factorGraph (layout (k:=k) E seed T P pre)).deg v ≤ 100000000*⌈((b:ℝ)^((3:ℝ)/4))⌉₊ := by
    apply ecPhysicalDegreeBound E seed T P pre hb v
    let A := ECWitCore.inner (k:=k) E seed T P pre
    by_contra! hn
    change A.ng+4*m ≤ v.val+4*m ∧ v.val < A.ng+4*m at hn
    let j : Fin (4*m) := ⟨v.val-A.ng,by omega⟩
    apply hv; apply Finset.mem_image.mpr
    refine ⟨(slotNumber (m:=m)).symm j,Finset.mem_univ _,?_⟩
    change Fin.castAdd A.nb (finSumFinEquiv (.inr (slotNumber (slotNumber.symm j)))) = v
    rw [Equiv.apply_symm_apply,finSumFinEquiv_apply_right]; apply Fin.ext; change A.ng+(v.val-A.ng)=v.val; omega
  have hq' : w3_ecQueries Q := hq₀
  have hh : 2 ≤ 100000000*⌈((b:ℝ)^((3:ℝ)/4))⌉₊ :=
    (DegreeInputs.small p 2 (by decide)).trans (DegreeInputs.cap_bound p hb)
  let W : w3_WireCore Q 100000000 := coreOfBounds (m:=m) (k:=k) (M:=g) (C:=100000000) (S:=100000000*m*b) E seed T P pre F ht (Nat.le_pow_clog (by decide) _) hF y w
    (by omega) (show 1 ≤ m by omega) (fun j => (hi j).1)
    (m3b_ec_layout_size E seed T P pre (show 1 ≤ m by omega) (show 1 ≤ b by omega) hk') hd hh shape
  have fit : ECFits.FitsCore (compiled w) (body (k:=k) E seed T P pre) :=
    m3b_ec_body_fits_core p E h1 h2 h3 p67 g64 hM seed F P y pre
  have hpacket : ecBuild Q.input=w3_wirePacket W :=
    DetDLP.M3B.packetFromLayout Q hq' (p:=p) (m:=m) (k:=k) (T:=T) E seed P pre rfl rfl rfl fit slotNumber.symm
  have bounds := allbounds (q:=Q) (C:=100000000) W hpacket
  refine ⟨W,hpacket,bounds.1,?_⟩
  intro v a
  exact ⟨bounds.2 v a,hen (m:=m) (k:=k) (M:=g) E seed T P pre F y w hq' fit v a⟩
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open DetDLP DetDLP.M3B.ECPolyDefs Groundwork

/-- From per-query ec wire-core existence, produce matching `ecBuild`/`ecEntry`
    packet witnesses for some polynomial degree budget `c`. -/

theorem DetDLP.M3B.ECWitness.nativeQueryWitness
    (hcore : ∀ q, w3_ecQueries q →
      ∃ W : w3_WireCore q 100000000, W.desc = q.input ∧ W.S = 100000000 * q.m * q.b) :
    ∃ c : ℕ, 0 < c ∧
      ∀ q, w3_ecQueries q → ∃ W : w3_WireCore q 100000000,
        ecBuild q.input = w3_wirePacket W ∧
        W.G.subdivision.nV ≤ (W.S + W.desc.length + 1) ^ c ∧
        ∀ (v : Fin W.G.subdivision.nV) (a : Fin (W.G.subdivision.deg v) → Bool),
          let w := encodePortQuery W.desc v.val (List.ofFn a)
          w.length + 1 ≤ (W.S + W.desc.length + 1) ^ c ∧
          EncodesTruncPoly (w3_precision q) (w3_len q) (ecEntry w)
            (w3_liftTensor W.G W.T v a)  := by
  apply M3B.ECWitness.witness_of_entries _ hcore
  intro p m k M prime nz E ell seed T P η F y input
  dsimp only
  intro hq fit v a
  exact M3B.ECWitness.native_entries (m:=m) (k:=k) (M:=M) E seed T P η F y input hq fit v a

end

open DetDLP DetDLP.M3B

private theorem nativeECWiring : w3_polyWireFamily w3_ecQueries := by
  obtain ⟨c,hc,hw⟩ := ECWitness.nativeQueryWitness m3b_ec_wire_core_exists
  exact ⟨100000000,c,ECPolyDefs.ecBuild,ECPolyDefs.ecEntry,by decide,hc,m3b_ec_build_poly,m3b_ec_entry_poly,hw⟩

end

set_option autoImplicit false
namespace DetDLP

private theorem y_eq_of_parity {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    {E : WeierstrassCurve (ZMod p)} (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    {x y z : ZMod p} (hy : E.toAffine.Equation x y) (hz : E.toAffine.Equation x z)
    (par : y.val % 2 = z.val % 2) : y = z := by
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq hy hz rfl with eq | neg
  · exact eq
  · have h : y = -z := by
      simpa only [WeierstrassCurve.Affine.negY,h₁,h₃,zero_mul,sub_zero] using neg
    by_cases h0 : z = 0
    · simpa only [h0,neg_zero] using h
    · let _ : NeZero z := ⟨h0⟩
      have hv := congrArg ZMod.val h
      rw [ZMod.val_neg_of_ne_zero] at hv
      obtain ⟨k,hk⟩ := (Fact.out : Nat.Prime p).odd_of_ne_two (by omega)
      have hzp := z.val_lt
      omega

/-- Parity fixes the affine hash seed, and the hash residue together with
parity determines a unique point of the selected block. -/
theorem ecSeparatorBlockCard {p m : ℕ} [Fact p.Prime] (hp : 2 < p)
    (E : WeierstrassCurve (ZMod p)) (h₁ : E.a₁=0) (h₃ : E.a₃=0)
    (T : ℕ) (S : ECSeed p m) (i : Fin m) : (ecFactorBlock E T S i).card ≤ 2*T := by
  let side (y : ZMod p) : Fin 2 := ⟨y.val % 2, Nat.mod_lt _ (by decide)⟩
  let a (s : Fin 2) := (S i (decide (s.val=1))).1.val + 1
  let b (s : Fin 2) := (S i (decide (s.val=1))).2.val
  let hash (s : Fin 2) (x : ZMod p) := (a s*x.val+b s)%p
  have hash_inj (s : Fin 2) : Function.Injective (hash s) := by
    have bound : a s < p := by have h := (S i (decide (s.val=1))).1.isLt; dsimp [a]; omega
    have nz : (a s : ZMod p) ≠ 0 := by
      intro h
      have eq := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt bound,ZMod.val_zero] at eq
      dsimp [a] at eq
      omega
    intro x z h
    have eq := congrArg (fun k : ℕ => (k : ZMod p)) h
    simp only [hash,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,ZMod.natCast_val,ZMod.cast_id] at eq
    exact mul_left_cancel₀ nz (add_right_cancel eq)
  let key : E.toAffine.Point → Fin 2 × ℕ
    | .zero => (0,0)
    | .some x y _ => (side y,hash (side y) x)
  have lt (P : E.toAffine.Point) (h : P ∈ ecFactorBlock E T S i) : (key P).2 < T := by
    have ok := (Finset.mem_filter.mp h).2
    cases P with
    | zero => contradiction
    | some x y _ => exact of_decide_eq_true ok
  let code (P : ↥(ecFactorBlock E T S i)) : Fin 2 × Fin T :=
    ((key P.val).1,⟨(key P.val).2,lt P.val P.property⟩)
  have inj : Function.Injective code := by
    rintro ⟨P,hP⟩ ⟨Q,hQ⟩ eq
    apply Subtype.ext
    cases P with
    | zero => exact False.elim (by have := (Finset.mem_filter.mp hP).2; contradiction)
    | some x y hy =>
      cases Q with
      | zero => exact False.elim (by have := (Finset.mem_filter.mp hQ).2; contradiction)
      | some u z hz =>
        have hs : side y = side z := congrArg Prod.fst eq
        have hh : hash (side y) x = hash (side z) u := congrArg (fun q : Fin 2 × Fin T => q.2.val) eq
        rw [hs] at hh
        obtain rfl := hash_inj (side z) hh
        obtain rfl := y_eq_of_parity hp h₁ h₃ hy.1 hz.1 (congrArg Fin.val hs)
        rfl
  simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] using
    Fintype.card_le_of_injective code inj

end DetDLP

set_option autoImplicit false
open DetDLP

theorem solution : w3_Separator w3_ecQueries := by
  refine w3_compile_wire_separator _ ?_ nativeECWiring
  intro q hq
  obtain ⟨p,hp,E,hE,ha1,_,ha3,h67,h64,_,_,seed,F,hF,P,y,pre,rfl⟩ := hq
  let _ := ecPointFintype E
  let M := Fintype.card E.toAffine.Point
  let m := blockCount (bitLen p)
  let T := hashThreshold p (M-1) m M
  refine ⟨le_max_left 2 _,by dsimp only; omega,?_⟩
  intro i
  change (F i).length ≤ 2^Nat.clog 2 (2*T)
  rw [←List.toFinset_card_of_nodup (hF i).1,(hF i).2]
  exact (ecSeparatorBlockCard (by omega) E ha1 ha3 T seed i).trans (Nat.le_pow_clog (by decide) _)
