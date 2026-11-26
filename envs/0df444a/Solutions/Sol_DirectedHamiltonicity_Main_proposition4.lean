-- Prove2me | solution 1 for DirectedHamiltonicity.Main.proposition4
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:46:06.855564+00:00
-- url     : https://prove2.me/submissions/ea01259b-2f81-47d4-a6ab-83f60a313405

import Theorems.Thm_AffinePrefixEnumeration_solver_exists
import Theorems.Thm_DirectedHamiltonicity_Main_InputRAM_TrialParameters_bootstrap_exec
import Theorems.Thm_DirectedHamiltonicity_Main_InputRAM_TrialParameters_runTrials_exec
import Theorems.Thm_DirectedHamiltonicity_Main_InputRAM_bounded_of_valid_body
import Theorems.Thm_DirectedHamiltonicity_Main_InputRAM_prepareRequest_exec
import Theorems.Thm_DirectedHamiltonicity_Main_lemma10
import Theorems.Thm_DirectedHamiltonicity_Main_lemma8
import Theorems.Thm_DirectedHamiltonicity_Main_lemma9
import Theorems.Thm_EditGV897_Main_affine_count_correct
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_native_integer_determinant
import Theorems.Thm_TargetedSamplers_Structured_StackMachine_fields_call

set_option autoImplicit false

section LogCostWordBounds

/-! Bit-cost bounds for bounded-width executions on the published log-cost RAM. -/

namespace TargetedSamplers

theorem size_add_le_succ {u v b : ℕ} (hu : u.size ≤ b) (hv : v.size ≤ b) :
    (u + v).size ≤ b + 1 := by
  rw [Nat.size_le] at *
  rw [pow_succ]
  omega

end TargetedSamplers

end LogCostWordBounds

section StructuredLogCostRAM

/-! Structured, relocatable programs for the Prove2Me log-cost machine. All costs count
the primitive steps of the published instruction list, including jumps. -/

namespace TargetedSamplers.Structured

theorem Exec.post {τ inv c s t k} (e : Exec τ inv c s t k) (hs : inv s) : inv t := by
  induction e <;> solve_by_elim

/-- A live, ordinary machine state at the specified instruction, memory and output. -/
structure Located (st : State) (pc : ℕ) (s : Store) : Prop where
  counter : st.pc = pc
  live : st.halted = false
  normal : st.bot = false
  memory : st.mem = s.mem
  output : st.out = s.out

private theorem step_op {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (p : Op) (hp : P[pc]? = some p.instruction) : Located (P.step τ st) (pc+1) (p.eval τ s) := by
  obtain ⟨hc,hh,hb,hm,ho⟩ := h
  cases p <;> constructor <;> simp_all [Op.instruction, Op.eval, Program.step, State.write, Store.write]

end TargetedSamplers.Structured

end StructuredLogCostRAM

section StructuredLogCostFragments

namespace TargetedSamplers.Structured

theorem Store.write_fits {s : Store} {width v : ℕ} (h : s.Fits width) (d : ℕ) (hv : v.size ≤ width) :
    (s.write d v).Fits width := by
  intro a
  by_cases he : a = d
  · simpa [Store.write, he] using hv
  · simpa [Store.write, he] using h a

def Op.written (τ : Tapes) (s : Store) : Op → ℕ
  | .const _ c => c
  | .add _ a b => s.mem a + s.mem b
  | .sub _ a b => s.mem a - s.mem b
  | .load _ a => s.mem (s.mem a)
  | .store _ b => s.mem b
  | .input _ a => bitVal τ.input[s.mem a]?
  | .coin _ a => bitVal τ.coins[s.mem a]?
  | .output _ => 0

theorem Op.eval_fits (p : Op) (τ : Tapes) {s : Store} {b : ℕ}
    (hi : s.Fits b) (hw : (p.written τ s).size ≤ b) : (p.eval τ s).Fits b := by
  cases p <;> first | exact Store.write_fits hi _ hw | exact hi

structure Result where
  last : Store
  steps : ℕ
  writeWidth : ℕ

/-- Evaluation charges the actual control transfers and records the largest value written. -/
def Fragment.run (τ : Tapes) (s : Store) : Fragment → Result
  | .skip => ⟨s,0,0⟩
  | .op o => ⟨o.eval τ s,1,(o.written τ s).size⟩
  | .seq x y =>
    let p := x.run τ s
    let q := y.run τ p.last
    ⟨q.last,p.steps+q.steps,max p.writeWidth q.writeWidth⟩
  | .branch a b yes no =>
    if s.mem a ≤ s.mem b then
      let p := yes.run τ s
      ⟨p.last,1+p.steps,p.writeWidth⟩
    else
      let p := no.run τ s
      ⟨p.last,1+p.steps+1,p.writeWidth⟩

theorem Fragment.exec (f : Fragment) (τ : Tapes) (s : Store) (b : ℕ)
    (hs : s.Fits b) (hw : (f.run τ s).writeWidth ≤ b) :
    Exec τ (fun st => st.Fits b) f.cmd s (f.run τ s).last (f.run τ s).steps := by
  induction f generalizing s with
  | skip => exact .skip s
  | op o => exact .op s o (o.eval_fits τ hs hw)
  | seq x y ix iy =>
    obtain ⟨hx,hy⟩ := max_le_iff.mp hw
    have first := ix s hs hx
    exact .seq first (iy _ (first.post hs) hy)
  | branch a b y n iy ino =>
    by_cases h : s.mem a ≤ s.mem b
    · simp only [run,h,if_true] at hw ⊢
      exact .yes h (iy s hs hw)
    · simp only [run,h,if_false] at hw ⊢
      exact .no h (ino s hs hw)

end TargetedSamplers.Structured

end StructuredLogCostFragments

section LogCostRAMRanges

namespace TargetedSamplers.Structured

/-- An ascending loop can charge each iteration separately. A cumulative cost
bound permits output-sensitive enumeration even when one trial returns many words. -/
theorem forRange_exec_budget {τ : Tapes} {b : ℕ} (ptr stop one lo count : ℕ) (budget : ℕ → ℕ) (body : Cmd)
    (state : ℕ → Store → Prop)
    (control : ∀ i ≤ count, ∀ s, state i s → s.mem ptr = lo+i ∧ s.mem stop = lo+count)
    (bodyRun : ∀ i < count, ∀ s, state i s → s.Fits b →
      ∃ u k, Exec τ (fun st => st.Fits b) body s u k ∧ budget i+k+3 ≤ budget (i+1) ∧ u.mem ptr = lo+i ∧ u.mem one = 1 ∧
        state (i+1) (u.write ptr (lo+i+1)))
    (width : (lo+count).size ≤ b) (s : Store) (start : state 0 s) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (forRange ptr stop one body) s t j ∧
      budget 0+j ≤ budget count+1 ∧ state count t := by
  have run (left i : ℕ) (he : i+left = count) (u : Store) (hi : state i u) (hf : u.Fits b) :
      ∃ t j, Exec τ (fun st => st.Fits b) (forRange ptr stop one body) u t j ∧
        budget i+j ≤ budget count+1 ∧ state count t := by
    induction left generalizing i u with
    | zero =>
      have eq : i = count := by omega
      obtain ⟨hp,hs⟩ := control i (by omega) u hi
      exact ⟨u,1,.done (by rw [hs,hp,eq]),by rw [eq],eq ▸ hi⟩
    | succ left ih =>
      obtain ⟨hp,hs⟩ := control i (by omega) u hi
      obtain ⟨v,k,ex,hk,hp',h1,hn⟩ := bodyRun i (by omega) u hi hf
      have hnext : (Op.add ptr ptr one).eval τ v = v.write ptr (lo+i+1) := by simp [Op.eval,hp',h1]
      have hiw := (Nat.size_le_size (show lo+i+1 ≤ lo+count by omega)).trans width
      have inc : Exec τ (fun st => st.Fits b) (.op (.add ptr ptr one)) v (v.write ptr (lo+i+1)) 1 := by
        simpa only [hnext] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) v (.add ptr ptr one)
          (by rw [hnext]; exact Store.write_fits (ex.post hf) ptr hiw))
      obtain ⟨t,j,loop,hj,ret⟩ := ih (i+1) (by omega) _ hn (inc.post (ex.post hf))
      refine ⟨t,_,.again (by rw [hs,hp]; omega) (ex.seq inc) loop,?_,ret⟩
      omega
  exact run count 0 (by simp) s start fit

/-- The outer loop pays once per trial and once per returned word. The result keeps
both counts separate so that a cap on their total gives a linear trial budget. -/
theorem forRange_exec_reported {τ : Tapes} {b : ℕ} (ptr stop one count setup perWord : ℕ)
    (reports : ℕ → ℕ) (body : Cmd) (state : ℕ → Store → Prop)
    (control : ∀ i ≤ count, ∀ s, state i s → s.mem ptr=i ∧ s.mem stop=count)
    (bodyRun : ∀ i < count, ∀ s, state i s → s.Fits b →
      ∃ u k, Exec τ (fun st => st.Fits b) body s u k ∧ k ≤ setup+reports i*perWord ∧
        u.mem ptr=i ∧ u.mem one=1 ∧ state (i+1) (u.write ptr (i+1)))
    (width : count.size ≤ b) (s : Store) (start : state 0 s) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (forRange ptr stop one body) s t j ∧
      j ≤ count*(setup+3)+prefixReports reports count*perWord+1 ∧ state count t := by
  let budget := fun i => i*(setup+3)+prefixReports reports i*perWord
  obtain ⟨t,j,ex,cost,post⟩ := forRange_exec_budget (τ := τ) ptr stop one 0 count budget body state
    (by simpa only [Nat.zero_add] using control) (fun i hi u hu fu => by
      obtain ⟨v,k,run,work,ptr,unit,next⟩ := bodyRun i hi u hu fu
      refine ⟨v,k,run,?_,by simpa using ptr,unit,by simpa using next⟩
      simp only [budget,prefixReports,Nat.succ_mul,Nat.add_mul]
      omega) (by simpa using width) s start fit
  exact ⟨t,j,ex,by simpa [budget,prefixReports] using cost,post⟩

end TargetedSamplers.Structured

end LogCostRAMRanges

section BoundedBinaryInput

/-! A bounded reader for little-endian self-delimiting naturals. Each payload bit is
preceded by a one; a zero marker terminates the field. -/

namespace BoundedBinaryInput

private def payload (bs : List Bool) : List Bool := bs.flatMap fun b => [true, b]

private theorem read_payload (k : ℕ) (bs rest : List Bool) :
    read k (payload bs ++ false :: rest) =
      if bs.length ≤ k then some (bs.foldr Nat.bit 0) else none := by
  induction bs generalizing k with
  | nil => cases k <;> rfl
  | cons b bs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      change (read k (payload bs ++ false :: rest)).map (Nat.bit b) = _
      rw [ih]
      by_cases h : bs.length ≤ k <;> simp [h]

theorem fold_bits (x : ℕ) : x.bits.foldr Nat.bit 0 = x := by
  induction x using Nat.binaryRec' with
  | zero => rfl
  | bit b x h ih => simp [Nat.bits_append_bit x b h, ih]

/-- Returns the original value if it fits, and rejects an oversized numeral independently
of its uninspected high digits or the contents of the following fields. -/
theorem read_encoded (k x : ℕ) (rest : List Bool) :
    read k ((x.bits.flatMap (fun b => [true, b])) ++ false :: rest) =
      if x.size ≤ k then some x else none := by
  simpa only [payload, Nat.size_eq_bits_len, fold_bits] using read_payload k x.bits rest

theorem readAtMost_encoded (cap x : ℕ) (rest : List Bool) :
    readAtMost cap ((x.bits.flatMap (fun b => [true, b])) ++ false :: rest) =
      if x ≤ cap then some x else none := by
  rw [readAtMost, read_encoded]
  by_cases hx : x ≤ cap
  · simp [hx, Nat.size_le_size hx]
  · by_cases hs : x.size ≤ cap.size <;> simp [hs, hx]

end BoundedBinaryInput

end BoundedBinaryInput

section HamiltonianArcAggregation

namespace DirectedHamiltonicity.Main.Multidigraph

open scoped BigOperators

open Classical

private def profileEquiv {I E F : Type} (f : E → F) :
    (Σ p : I → F, (i : I) → {x : E // f x = p i}) ≃ (I → E) :=
  (Equiv.sigmaCongrRight (fun p =>
    (⟨fun g => ⟨fun i => (g i).1, funext fun i => (g i).2⟩,
      fun q i => ⟨q.1 i, congrFun q.2 i⟩, fun _ => rfl, fun _ => rfl⟩ :
      ((i : I) → {x : E // f x = p i}) ≃ {q : I → E // f ∘ q = p}))).trans
    (Equiv.sigmaFiberEquiv fun q : I → E => f ∘ q)

variable {V E F K : Type} [Fintype V] [Fintype E] [Fintype F] [CommRing K]

variable (H : Multidigraph V E) (G : Multidigraph V F) (f : E → F)

variable (htail : ∀ e, G.tail (f e) = H.tail e) (hhead : ∀ e, G.head (f e) = H.head e)

omit [Fintype E] [Fintype F] in
include htail hhead in
private theorem isPath_map_arcs (s t : V) (q : Fin (Fintype.card V - 1) → E) :
    G.IsHamPath s t (f ∘ q) ↔ H.IsHamPath s t q := by
  have hv : G.walkVerts s (f ∘ q) = H.walkVerts s q := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact hhead (q j)
  simp only [IsHamPath, hv, Function.comp_apply, htail]

noncomputable def arcLabelSum (f : E → F) (p : E → K) (a : F) : K := ∑ e : {e // f e = a}, p e.1

omit [Fintype F] in
theorem arcLabelSum_constant (f : E → F) (p : E → K) (a : F) (u : K) (hu : ∀ e, f e = a → p e = u) :
    arcLabelSum f p a = (Nat.card {e // f e = a} : K) * u := by
  classical
  unfold arcLabelSum
  calc
    _ = ∑ _ : {e // f e = a}, u := Finset.sum_congr rfl fun e _ => hu e.1 e.2
    _ = _ := by simp [Nat.card_eq_fintype_card, nsmul_eq_mul]

include htail hhead in
/-- Aggregating arcs with the same endpoints adds their labels, preserving the whole
Hamiltonian path generating polynomial over any commutative ring. -/
theorem hamPathPoly_map_arcs (p : E → K) (s t : V) :
    H.hamPathPoly p s t = G.hamPathPoly (arcLabelSum f p) s t := by
  classical
  unfold arcLabelSum
  let I := Fin (Fintype.card V - 1)
  let term := fun q : I → E => if G.IsHamPath s t (f ∘ q) then ∏ i, p (q i) else 0
  calc
    _ = ∑ q : I → E, term q := by
      simp only [hamPathPoly, hamPaths, Finset.sum_filter, term]
      apply Finset.sum_congr rfl
      intro q _
      rw [isPath_map_arcs H G f htail hhead]
    _ = ∑ q : Σ g : I → F, (i : I) → {e : E // f e = g i}, term (profileEquiv f q) :=
      ((profileEquiv f).sum_comp term).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [hamPathPoly, hamPaths, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro g _
      have hp (v : (i : I) → {e : E // f e = g i}) :
          f ∘ profileEquiv f ⟨g,v⟩ = g := funext fun i => (v i).2
      simp only [term, hp]
      by_cases h : G.IsHamPath s t g
      · simp only [if_pos h]
        symm
        simpa [profileEquiv] using Finset.prod_univ_sum
          (fun i : I => (Finset.univ : Finset {e : E // f e = g i}))
          (fun _ e => p e.1)
      · simp [h]

omit [Fintype E] in
/-- Each arc of a Hamiltonian path has distinct endpoints, avoids entering its start,
and avoids leaving its end. -/
theorem IsHamPath.arc_allowed {s t : V} {q : Fin (Fintype.card V - 1) → E}
    (hq : H.IsHamPath s t q) (i : Fin (Fintype.card V - 1)) :
    H.tail (q i) ≠ H.head (q i) ∧ H.head (q i) ≠ s ∧ H.tail (q i) ≠ t := by
  let v := H.walkVerts s q
  have hinj : Function.Injective v := hq.2.1
  have h₁ : H.tail (q i) = v i.castSucc := hq.1 i
  have h₂ : H.head (q i) = v i.succ := rfl
  have hs : v 0 = s := rfl
  have ht : v (Fin.last _) = t := hq.2.2
  rw [h₁, h₂, ← hs, ← ht]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrArg Fin.val (hinj h); simp at this
  · have := congrArg Fin.val (hinj h); simp at this
  · have := congrArg Fin.val (hinj h); simp at this; omega

/-- Arcs outside a restriction can be removed whenever every path using one of them
has zero label on that arc. -/
theorem hamPathPoly_restrict_of_zero (p : E → K) (s t : V) (keep : E → Prop)
    (hz : ∀ q, H.IsHamPath s t q → ∀ i, ¬keep (q i) → p (q i) = 0) :
    H.hamPathPoly p s t = (H.restrictArcs keep).hamPathPoly (fun e => p e.1) s t := by
  classical
  let G := H.restrictArcs keep
  let I := Fin (Fintype.card V - 1)
  let emb : (I → {e // keep e}) ↪ (I → E) :=
    ⟨fun q i => (q i).1, fun _ _ h => funext fun i => Subtype.ext (congrFun h i)⟩
  have hpath (q : I → {e // keep e}) : H.IsHamPath s t (emb q) ↔ G.IsHamPath s t q :=
    isPath_map_arcs G H Subtype.val (fun _ => rfl) (fun _ => rfl) s t q
  have hsub : (G.hamPaths s t).map emb ⊆ H.hamPaths s t := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hpath v).mpr (Finset.mem_filter.mp hv).2⟩
  calc
    _ = ∑ q ∈ (G.hamPaths s t).map emb, ∏ i, p (q i) := by
      symm
      apply Finset.sum_subset hsub
      intro q hq hmiss
      have hp := (Finset.mem_filter.mp hq).2
      have h : ¬ ∀ i, keep (q i) := by
        intro hall
        let v := fun i => (⟨q i, hall i⟩ : {e // keep e})
        have hv : G.IsHamPath s t v := (hpath v).mp hp
        exact hmiss (Finset.mem_map.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩)
      obtain ⟨i, hi⟩ := Classical.not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hz q hp i hi)
    _ = _ := by
      rw [Finset.sum_map]
      rfl

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianArcAggregation

section HamiltonianParityNormalization

namespace DirectedHamiltonicity.Main.Multidigraph

open Polynomial Classical

open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E]

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V) {W : ℕ} (hw : ∀ e, w e ≤ W)

omit [Fintype V] [Fintype E] in
theorem normalizedGraph_isNormalized :
    (H.normalizedGraph w s t hw).IsNormalized (H.normalizedWeight w s t hw) s t := by
  refine ⟨fun e => e.2.1, fun e => e.2.2.1, fun e => e.2.2.2.1, ?_⟩
  intro e f hef ht hh hweight
  apply hef
  apply Subtype.ext
  exact Prod.ext ht (Prod.ext hh (Fin.ext hweight))

theorem normalizedGraph_incomingWeights (v : V) :
    (H.normalizedGraph w s t hw).incomingWeights (H.normalizedWeight w s t hw) v ⊆
      H.incomingWeights w v := by
  classical
  intro b hb
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
  have hh := (Finset.mem_filter.mp hq).2
  have hodd : Odd (Fintype.card {e : E // H.arcType w hw e = q.1}) := by
    rw [← Nat.card_eq_fintype_card]
    exact q.2.2.2.2
  have pos : 0 < Fintype.card {e : E // H.arcType w hw e = q.1} := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at hodd
  obtain ⟨e, he⟩ := Fintype.card_pos_iff.mp pos
  refine Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · exact (congrArg (fun j : ArcType V W => j.2.1) he).trans hh
  · exact congrArg (fun j : ArcType V W => j.2.2.val) he

/-- Group equal-weight parallel arcs by their triple. In characteristic two only triples of
odd multiplicity survive; loops and arcs entering the start or leaving the end cannot occur. -/
theorem normalizedGraph_pathPolynomial :
    H.hamPathPoly (fun e => (X : (ZMod 2)[X]) ^ w e) s t =
      (H.normalizedGraph w s t hw).hamPathPoly
        (fun e => (X : (ZMod 2)[X]) ^ H.normalizedWeight w s t hw e) s t := by
  classical
  let G := allArcs V W
  let f := H.arcType w hw
  let label := arcLabelSum f (fun e => (X : (ZMod 2)[X]) ^ w e)
  have lab (q : ArcType V W) : label q =
      if Odd (Nat.card {e // f e = q}) then X ^ q.2.2.val else 0 := by
    have hwq (e : E) (he : f e = q) : w e = q.2.2.val :=
      congrArg (fun j : ArcType V W => j.2.2.val) he
    dsimp only [label]
    rw [arcLabelSum_constant f _ q (X ^ q.2.2.val) (fun e he => congrArg (fun b => X ^ b) (hwq e he))]
    rw [← map_natCast (Polynomial.C : ZMod 2 →+* (ZMod 2)[X]) (Nat.card {e // f e = q})]
    by_cases ho : Odd (Nat.card {e // f e = q})
    · rw [if_pos ho, ZMod.natCast_eq_one_iff_odd.mpr ho, map_one, one_mul]
    · rw [if_neg ho, ZMod.natCast_eq_zero_iff_even.mpr (Nat.not_odd_iff_even.mp ho), map_zero, zero_mul]
  have hzero : ∀ q, G.IsHamPath s t q → ∀ i, ¬H.retainArc w s t hw (q i) → label (q i) = 0 := by
    intro q hp i hn
    obtain ⟨h₁,h₂,h₃⟩ := IsHamPath.arc_allowed G hp i
    have hodd : ¬Odd (Nat.card {e // f e = q i}) := fun h => hn ⟨h₁,h₂,h₃,h⟩
    exact (lab (q i)).trans (if_neg hodd)
  calc
    _ = G.hamPathPoly label s t := H.hamPathPoly_map_arcs G f (fun _ => rfl)
      (fun _ => rfl) (fun e => (X : (ZMod 2)[X]) ^ w e) s t
    _ = (H.normalizedGraph w s t hw).hamPathPoly (fun e => label e.1) s t :=
      G.hamPathPoly_restrict_of_zero label s t (H.retainArc w s t hw) hzero
    _ = _ := by
      apply congrArg (fun p => (H.normalizedGraph w s t hw).hamPathPoly p s t)
      funext e
      exact (lab e.1).trans (if_pos e.2.2.2.2)

/-- Each retained triple has an original arc over it, so normalization never increases
the number of arcs. -/
theorem normalizedGraph_card_le : Fintype.card (H.RetainedArc w s t hw) ≤ Fintype.card E := by
  classical
  have rep (q : H.RetainedArc w s t hw) : Nonempty {e : E // H.arcType w hw e = q.1} := by
    apply Fintype.card_pos_iff.mp
    by_contra! hc
    have h : Odd (Fintype.card {e : E // H.arcType w hw e = q.1}) := by
      rw [← Nat.card_eq_fintype_card]
      exact q.2.2.2.2
    simp [Nat.eq_zero_of_le_zero hc] at h
  let pick := fun q => (rep q).some
  apply Fintype.card_le_of_injective (fun q => (pick q).1)
  intro a b h
  exact Subtype.ext (((pick a).2.symm.trans (congrArg (H.arcType w hw) h)).trans (pick b).2)

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianParityNormalization

section LogCostRAMCompare

namespace TargetedSamplers.Structured

/-- Compare words using the native non-strict comparison. Equal words take two jumps;
unequal words take at most three before and after executing the selected arm. -/
theorem ifEqual_exec {τ : TargetedSamplers.Tapes} {I : Store → Prop} (l r : ℕ)
    {yes no : Cmd} {s t : Store} {k : ℕ} (h : Exec τ I (if s.mem l=s.mem r then yes else no) s t k) :
    ∃ j ≤ k+3, Exec τ I (ifEqual l r yes no) s t j := by
  by_cases eq : s.mem l = s.mem r
  · rw [if_pos eq] at h
    exact ⟨_,by omega,.yes eq.le (.yes eq.ge h)⟩
  · rw [if_neg eq] at h
    by_cases le : s.mem l ≤ s.mem r
    · exact ⟨_,by omega,.yes le (.no (by omega) h)⟩
    · exact ⟨_,by omega,.no le h⟩

def allEqual (s : Store) (xs : List (ℕ × ℕ)) := xs.all fun p => decide (s.mem p.1 = s.mem p.2)

theorem whenEqual_exec {τ : TargetedSamplers.Tapes} {I : Store → Prop} (tests : List (ℕ × ℕ)) (body : Cmd)
    {s t : Store} {k : ℕ} (h : Exec τ I (if allEqual s tests then body else .skip) s t k) :
    ∃ j ≤ k+3*tests.length, Exec τ I (whenEqual tests body) s t j := by
  induction tests with
  | nil => exact ⟨k,by simp,by simpa [whenEqual,allEqual] using h⟩
  | cons test rest ih =>
    obtain ⟨a,b⟩ := test
    have head : allEqual s ((a,b)::rest) = (decide (s.mem a = s.mem b) && allEqual s rest) := rfl
    rw [head] at h
    by_cases eq : s.mem a = s.mem b
    · rw [decide_eq_true eq, Bool.true_and] at h
      obtain ⟨j,hj,run⟩ := ih h
      obtain ⟨i,hi,exec⟩ := ifEqual_exec (τ := τ) (I := I) a b (yes := whenEqual rest body) (no := .skip)
        (s := s) (t := t) (k := j) (by simpa only [if_pos eq] using run)
      exact ⟨i,by simp only [List.length_cons]; omega,exec⟩
    · have skip : Exec τ I .skip s t k := by simpa only [decide_eq_false eq, Bool.false_and, Bool.false_eq_true, if_false] using h
      obtain ⟨j,hj,exec⟩ := ifEqual_exec (τ := τ) (I := I) a b (yes := whenEqual rest body) (no := .skip)
        (s := s) (t := t) (k := k) (by simpa only [if_neg eq] using skip)
      exact ⟨j,by simp only [List.length_cons]; omega,exec⟩

end TargetedSamplers.Structured

end LogCostRAMCompare

section LogCostRAMTripleParity

namespace TargetedSamplers.Structured.TripleScan

theorem RecordsAt.congr {s t : Store} {base : ℕ} {xs : List Record}
    (h : RecordsAt s base xs) (same : ∀ a ≥ base, t.mem a = s.mem a) : RecordsAt t base xs := by
  induction xs generalizing base with
  | nil => trivial
  | cons x xs ih =>
    exact ⟨(same _ le_rfl).trans h.1,(same _ (by omega)).trans h.2.1,
      (same _ (by omega)).trans h.2.2.1,ih h.2.2.2 (fun a ha => same a (by omega))⟩

def wanted (r : Fin 10 ↪ ℕ) (s : Store) : Record := (s.mem (r 3),s.mem (r 4),s.mem (r 5))

private theorem readFields_exec {τ : Tapes} {b : ℕ} (r : Fin 10 ↪ ℕ) (s : Store) (p : ℕ)
    (ptr : s.mem (r 0) = p) (one : s.mem (r 2) = 1) (sep : ∀ i, r i < p)
    (fit : s.Fits b) (width : (p+3).size ≤ b) :
    let t := ((readFields r).run τ s).last
    Exec τ (fun u => u.Fits b) (readFields r).cmd s t 6 ∧ t.mem (r 0) = p+3 ∧
      t.mem (r 7) = s.mem p ∧ t.mem (r 8) = s.mem (p+1) ∧ t.mem (r 9) = s.mem (p+2) ∧
      t.out = s.out ∧ ∀ a, a ≠ r 0 → a ≠ r 7 → a ≠ r 8 → a ≠ r 9 → t.mem a = s.mem a := by
  have eq (i j : Fin 10) : r i = r j ↔ i=j := r.injective.eq_iff
  have past (k : ℕ) (i : Fin 10) : p+k ≠ r i := by have := sep i; omega
  have w₁ := (Nat.size_le_size (show p+1 ≤ p+3 by omega)).trans width
  have w₂ := (Nat.size_le_size (show p+2 ≤ p+3 by omega)).trans width
  have ww : ((readFields r).run τ s).writeWidth ≤ b := by
    simp [readFields,sequence,Fragment.run,Op.eval,Op.written,Store.write,Function.update_apply,
      eq,ptr,one,Nat.add_assoc,past,w₁,w₂,width,fit p,fit (p+1),fit (p+2)]
  refine ⟨(readFields r).exec τ s b fit ww,?_,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (intro a h₀ h₇ h₈ h₉
       simp [readFields,sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,h₀,h₇,h₈,h₉])
    | simp [readFields,sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,eq,ptr,one,Nat.add_assoc,past]

private theorem toggle_exec {τ : Tapes} {b : ℕ} (r : Fin 10 ↪ ℕ) (s : Store)
    (unit : s.mem (r 2) = 1) (fit : s.Fits b) :
    Exec τ (fun u => u.Fits b) (toggle r) s (s.write (r 6) (1-s.mem (r 6))) 1 := by
  have wh := (Nat.size_le_size (Nat.sub_le 1 (s.mem (r 6)))).trans (unit ▸ fit (r 2))
  simpa only [toggle,Op.eval,unit] using (Exec.op (τ := τ) (inv := fun u => u.Fits b)
    s (.sub (r 6) (r 2) (r 6)) (by simp only [Op.eval,unit]; exact Store.write_fits fit _ wh))

private theorem guardedToggle_exec {τ : Tapes} {b : ℕ} (r : Fin 10 ↪ ℕ) (s : Store)
    (hit : Bool) (matchBit : allEqual s (tests r) = hit) (one : s.mem (r 2) = 1) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (whenEqual (tests r) (toggle r)) s t j ∧ j ≤ 10 ∧
      t.mem (r 6) = (if hit then 1-s.mem (r 6) else s.mem (r 6)) ∧
      t.out = s.out ∧ ∀ a, a ≠ r 6 → t.mem a = s.mem a := by
  cases hit with
  | false =>
    obtain ⟨j,hj,ex⟩ := whenEqual_exec (tests r) (toggle r)
      (τ := τ) (I := fun u => u.Fits b) (s := s) (t := s) (k := 0)
      (by simp only [matchBit,Bool.false_eq_true,if_false]; exact .skip _)
    exact ⟨s,j,ex,by simp [tests] at hj; omega,rfl,rfl,fun _ _ => rfl⟩
  | true =>
    obtain ⟨j,hj,ex⟩ := whenEqual_exec (tests r) (toggle r)
      (τ := τ) (I := fun u => u.Fits b) (s := s) (t := s.write (r 6) (1-s.mem (r 6))) (k := 1)
      (by simp only [matchBit,if_true]; exact toggle_exec r s one fit)
    exact ⟨_,j,ex,by simpa [tests] using hj,by simp [Store.write],rfl,fun _ h => by simp [Store.write,h]⟩

/-- Read a triple, compare it with the query, and toggle a bit once for each match. -/
theorem loop_exec {τ : Tapes} {b : ℕ} (r : Fin 10 ↪ ℕ) (xs : List Record) (s : Store)
    (p v : ℕ) (q : Record) (data : RecordsAt s p xs) (ptr : s.mem (r 0) = p)
    (stop : s.mem (r 1) = p+3*xs.length) (unit : s.mem (r 2) = 1) (key : wanted r s = q)
    (acc : s.mem (r 6) = v) (bit : v ≤ 1) (sep : ∀ i, r i < p) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (loop r) s t j ∧ j ≤ 18*xs.length+1 ∧
      t.mem (r 0) = p+3*xs.length ∧ t.mem (r 6) = (v+xs.count q)%2 ∧ t.out = s.out ∧
      ∀ a, untouched r a → t.mem a = s.mem a := by
  induction xs generalizing s p v with
  | nil =>
    exact ⟨s,1,.done (by simpa [stop,ptr]),by simp,by simpa using ptr,
      by simpa [Nat.mod_eq_of_lt (show v < 2 by omega)] using acc,rfl,fun _ _ => rfl⟩
  | cons x xs ih =>
    have eq (i j : Fin 10) : r i = r j ↔ i=j := r.injective.eq_iff
    have endAt : s.mem (r 1) = p+3+3*xs.length := by rw [stop,List.length_cons]; omega
    let u := ((readFields r).run τ s).last
    obtain ⟨read,pos,h₇,h₈,h₉,out₁,fr₁⟩ := readFields_exec (τ := τ) r s p ptr unit sep fit
      ((Nat.size_le_size (show p+3 ≤ s.mem (r 1) by omega)).trans (fit _))
    have keep (i : Fin 10) (h : i ≠ 0 ∧ i ≠ 7 ∧ i ≠ 8 ∧ i ≠ 9) : u.mem (r i) = s.mem (r i) :=
      fr₁ _ (r.injective.ne h.1) (r.injective.ne h.2.1) (r.injective.ne h.2.2.1) (r.injective.ne h.2.2.2)
    have one : u.mem (r 2) = 1 := (keep 2 (by decide)).trans unit
    have matchBit : allEqual u (tests r) = decide (x = q) := by
      subst q
      rcases x with ⟨a,c,d⟩
      simp only [allEqual,tests,List.all_cons,List.all_nil, Bool.and_true, wanted,
        Prod.mk.injEq,Bool.decide_and]
      rw [h₇,h₈,h₉,data.1,data.2.1,data.2.2.1,keep 3 (by decide),keep 4 (by decide),keep 5 (by decide)]
    obtain ⟨z,k,guard,hk,val,out₂,fr₂⟩ := guardedToggle_exec (τ := τ) r u _ matchBit one (read.post fit)
    let next := if x=q then 1-v else v
    have vz : z.mem (r 6) = next := by simpa [next,keep 6 (by decide),acc] using val
    have frame (a : ℕ) (hp : untouched r a) : z.mem a = s.mem a :=
      (fr₂ a hp.2.1).trans (fr₁ a hp.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2)
    have regular (i : Fin 10) (hi : i ≠ 0 ∧ i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 8 ∧ i ≠ 9) : untouched r (r i) := by
      simpa only [untouched,ne_eq,eq] using hi
    have off (a : ℕ) (ha : p ≤ a) : untouched r a := by
      have outside (i : Fin 10) : a ≠ r i := by have := sep i; omega
      exact ⟨outside _,outside _,outside _,outside _,outside _⟩
    have kz : wanted r z = q := by
      simpa only [wanted,frame _ (regular 3 (by decide)),frame _ (regular 4 (by decide)),frame _ (regular 5 (by decide))] using key
    have posz := (fr₂ _ (r.injective.ne (by decide : (0:Fin 10) ≠ 6))).trans pos
    obtain ⟨t,j,rest,hj,last,result,out₃,fr₃⟩ := ih z (p+3) next
      (data.2.2.2.congr (fun a ha => frame a (off a (by omega)))) posz
      ((frame _ (regular 1 (by decide))).trans endAt) ((frame _ (regular 2 (by decide))).trans unit) kz vz
      (by dsimp [next]; split <;> omega) (fun i => by have := sep i; omega) (guard.post (read.post fit))
    refine ⟨t,_,.again (by rw [ptr,endAt]; omega) (read.seq guard) rest,
      by simp only [List.length_cons]; omega,by rw [last,List.length_cons]; omega,?_,
      out₃.trans (out₂.trans out₁),fun a ha => (fr₃ a ha).trans (frame a ha)⟩
    rw [result]
    by_cases eqx : x=q
    · subst x
      simp only [next,if_true,List.count_cons_self]
      omega
    · simp only [next,if_neg eqx,List.count_cons_of_ne eqx]

end TargetedSamplers.Structured.TripleScan

end LogCostRAMTripleParity

section LogCostRAMFilter

namespace TargetedSamplers.Structured

def anyEqual (s : Store) (xs : List (ℕ × ℕ)) := xs.any fun p => decide (s.mem p.1 = s.mem p.2)

theorem clearEqual_exec {τ : Tapes} {b : ℕ} (dst : ℕ) (xs : List (ℕ × ℕ)) (s : Store)
    (apart : ∀ p ∈ xs, p.1 ≠ dst ∧ p.2 ≠ dst) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (clearEqual dst xs) s t j ∧ j ≤ 4*xs.length ∧
      t.mem dst = (if anyEqual s xs then 0 else s.mem dst) ∧ t.out = s.out ∧
      ∀ a, a ≠ dst → t.mem a = s.mem a := by
  induction xs generalizing s with
  | nil => exact ⟨s,0,.skip _,by simp,rfl,rfl,fun _ _ => rfl⟩
  | cons p xs ih =>
    obtain ⟨a,c⟩ := p
    let u := if s.mem a = s.mem c then s.write dst 0 else s
    have run : ∃ j ≤ 4, Exec τ (fun u => u.Fits b) (ifEqual a c (.op (.const dst 0)) .skip) s u j := by
      by_cases eq : s.mem a = s.mem c
      · exact ifEqual_exec a c (s := s) (t := u) (k := 1)
          (by rw [if_pos eq]; dsimp [u]; rw [if_pos eq]; exact .op _ _ (Store.write_fits fit _ (by simp)))
      · obtain ⟨j,hj,ex⟩ := ifEqual_exec (τ := τ) (I := fun u => u.Fits b) a c
          (yes := .op (.const dst 0)) (no := .skip) (s := s) (t := u) (k := 0)
          (by rw [if_neg eq]; dsimp [u]; rw [if_neg eq]; exact .skip _)
        exact ⟨j,by omega,ex⟩
    obtain ⟨i,wi,first⟩ := run
    have keep (z : ℕ) (h : z ≠ dst) : u.mem z = s.mem z := by
      dsimp [u]; split <;> simp [Store.write,h]
    have tailApart (p : ℕ × ℕ) (hp : p ∈ xs) := apart p (List.mem_cons_of_mem _ hp)
    have same : anyEqual u xs = anyEqual s xs := by
      apply Bool.eq_iff_iff.mpr
      simp only [anyEqual,List.any_eq_true,decide_eq_true_eq]
      constructor <;> rintro ⟨p,hp,eq⟩ <;> refine ⟨p,hp,?_⟩ <;>
        simpa only [keep _ (tailApart p hp).1,keep _ (tailApart p hp).2] using eq
    obtain ⟨t,j,rest,wj,result,out,frame⟩ := ih u tailApart (first.post fit)
    refine ⟨t,_,first.seq rest,by simp only [List.length_cons]; omega,?_,?_,fun z hz => (frame z hz).trans (keep z hz)⟩
    · rw [result,same]
      change _ = (if (decide (s.mem a = s.mem c) || anyEqual s xs) then 0 else s.mem dst)
      by_cases eq : s.mem a = s.mem c <;> simp [u,eq,Store.write]
    · rw [out]; dsimp [u]; split <;> rfl

end TargetedSamplers.Structured

end LogCostRAMFilter

section HamiltonianRAMArcs

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.TripleScan

open Multidigraph

/-- Count queried triples in precisely the edge enumeration used by the external encoding. -/
theorem count_edgeRecords {n m W : ℕ} (tail head : Fin m → Fin n) (w : Fin m → ℕ)
    (hw : ∀ e, w e ≤ W) (q : ArcType (Fin n) W) :
    (edgeRecords tail head w).count (q.1.val,q.2.1.val,q.2.2.val) =
      Nat.card {e : Fin m // Multidigraph.arcType (⟨tail,head⟩ : Multidigraph (Fin n) (Fin m)) w hw e = q} := by
  classical
  let f (e : Fin m) : Record := ((tail e).val,(head e).val,w e)
  let test (e : Fin m) := Multidigraph.arcType (⟨tail,head⟩ : Multidigraph (Fin n) (Fin m)) w hw e = q
  let key : Record := (q.1.val,q.2.1.val,q.2.2.val)
  have he (e : Fin m) : f e = key ↔ test e := by
    rcases q with ⟨a,b,c⟩
    simp [f,key,test,arcType,Prod.ext_iff,Fin.ext_iff]
  have counts (es : List (Fin m)) : (es.map f).count key = es.countP fun e => decide (test e) := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      by_cases h : f e = key
      · simp [h,(he e).mp h,ih]
      · have hn : ¬test e := fun eq => h ((he e).mpr eq)
        simp [List.countP_cons,h,hn,ih]
  change ((List.finRange m).map f).count key = Nat.card {e : Fin m // test e}
  rw [counts,Nat.card_eq_fintype_card,Fintype.card_subtype,← (List.nodup_finRange m).card_eq_countP]
  simp

theorem retainedQuery_exec {τ : Tapes} {width : ℕ} {n m W : ℕ} (tail head : Fin m → Fin n)
    (w : Fin m → ℕ) (hw : ∀ e, w e ≤ W) (s t : Fin n) (q : ArcType (Fin n) W)
    (r : Fin 10 ↪ ℕ) (src dst base : ℕ) (u : Store) (records : RecordsAt u base (edgeRecords tail head w))
    (sep : ∀ i, r i < base) (ptr : u.mem (r 0) = base) (stop : u.mem (r 1) = base+3*m)
    (one : u.mem (r 2) = 1) (key : wanted r u = (q.1.val,q.2.1.val,q.2.2.val))
    (source : u.mem src = s.val) (sink : u.mem dst = t.val) (hs : untouched r src) (ht : untouched r dst)
    (fit : u.Fits width) :
    ∃ z j, Exec τ (fun v => v.Fits width) (retainedQuery r src dst) u z j ∧ j ≤ 18*m+14 ∧
      z.mem (r 6) ≤ 1 ∧ (z.mem (r 6) = 1 ↔ Multidigraph.retainArc (⟨tail,head⟩ : Multidigraph (Fin n) (Fin m)) w s t hw q) ∧
      z.mem (r 0) = base+3*m ∧ z.out = u.out ∧ ∀ a, untouched r a → z.mem a = u.mem a := by
  let v := u.write (r 6) 0
  have f : v.Fits width := Store.write_fits fit _ (by simp)
  have init : Exec τ (fun st => st.Fits width) (.op (.const (r 6) 0)) u v 1 := .op _ _ f
  have ne {i j : Fin 10} (h : i ≠ j) := r.injective.ne h
  have eq (i j : Fin 10) : r i = r j ↔ i=j := r.injective.eq_iff
  have atReg (i : Fin 10) (hi : i ≠ 6) : v.mem (r i) = u.mem (r i) := by simp [v,Store.write,ne hi]
  have keep (a : ℕ) (ha : untouched r a) : v.mem a = u.mem a := by simp [v,Store.write,ha.2.1]
  have len : (edgeRecords tail head w).length = m := by simp [edgeRecords]
  have records' : RecordsAt v base (edgeRecords tail head w) := records.congr (fun a ha => by
    have := sep 6; simp [v,Store.write,show a ≠ r 6 by omega])
  obtain ⟨a,i,scan,wi,pos,bit,out,frame⟩ := loop_exec (τ := τ) r (edgeRecords tail head w) v base 0
    (q.1.val,q.2.1.val,q.2.2.val) records' ((atReg 0 (by decide)).trans ptr) (by rw [len,atReg _ (by decide),stop])
    ((atReg 2 (by decide)).trans one) (by simpa only [wanted,atReg 3 (by decide),atReg 4 (by decide),atReg 5 (by decide)] using key)
    (by simp [v,Store.write]) (by decide) sep f
  rw [len] at wi pos
  rw [Nat.zero_add,count_edgeRecords tail head w hw q] at bit
  have fixes (p : ℕ × ℕ) (hp : p ∈ forbidden r src dst) : p.1 ≠ r 6 ∧ p.2 ≠ r 6 := by
    simp only [forbidden,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl
    · exact ⟨ne (by decide),ne (by decide)⟩
    · exact ⟨ne (by decide),hs.2.1⟩
    · exact ⟨ne (by decide),ht.2.1⟩
  obtain ⟨z,k,filter,wk,ret,out',fr⟩ := clearEqual_exec (τ := τ) (r 6) _ a fixes (scan.post f)
  have saved (ad : ℕ) (h : untouched r ad) := (frame ad h).trans (keep ad h)
  have reg (i : Fin 10) (h : i ≠ 0 ∧ i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 8 ∧ i ≠ 9) : untouched r (r i) := by
    simpa only [untouched,ne_eq,eq] using h
  have keys := Prod.mk.inj key
  have heads := Prod.mk.inj keys.2
  have bad : anyEqual a (forbidden r src dst) = decide (q.1 = q.2.1 ∨ q.2.1 = s ∨ q.1 = t) := by
    simp only [anyEqual,forbidden,List.any_cons,List.any_nil,Bool.or_false,
      saved _ (reg 3 (by decide)),saved _ (reg 4 (by decide)),saved _ hs,saved _ ht,
      keys.1,heads.1,source,sink,Bool.decide_or,Fin.ext_iff]
  simp only [bad,decide_eq_true_eq] at ret
  refine ⟨z,_,init.seq (scan.seq filter),by simp [forbidden] at wk; omega,?_,?_,
    (fr _ (ne (by decide))).trans pos,out'.trans out,fun ad ha => (fr ad ha.2.1).trans (saved ad ha)⟩
  · rw [ret]; split <;> omega
  · rw [ret,bit]
    by_cases h : q.1 = q.2.1 ∨ q.2.1 = s ∨ q.1 = t
    · rw [if_pos h]
      simp only [retainArc,Nat.odd_iff,Nat.zero_ne_one]
      tauto
    · rw [if_neg h]
      simp only [retainArc,Nat.odd_iff,Nat.zero_ne_one]
      tauto

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMArcs

section LogCostRAMFold

namespace TargetedSamplers.Structured

/-- The output tape and every address outside a finite register set are preserved. -/
structure Frame (dirty : Finset ℕ) (s t : Store) : Prop where
  output : t.out = s.out
  read : ∀ a ∉ dirty, t.mem a = s.mem a

theorem Frame.refl (dirty : Finset ℕ) (s : Store) : Frame dirty s s := ⟨rfl,fun _ _ => rfl⟩

theorem Frame.trans {dirty : Finset ℕ} {s t u : Store} (h : Frame dirty s t) (k : Frame dirty t u) :
    Frame dirty s u := ⟨k.output.trans h.output,fun a ha => (k.read a ha).trans (h.read a ha)⟩

theorem Frame.mono {small big : Finset ℕ} {s t : Store} (h : Frame small s t) (sub : small ⊆ big) :
    Frame big s t := ⟨h.output,fun a ha => h.read a (fun z => ha (sub z))⟩

theorem Frame.write {dirty : Finset ℕ} {s t : Store} (h : Frame dirty s t) (a : ℕ)
    (ha : a ∈ dirty) (x : ℕ) : Frame dirty s (t.write a x) := by
  refine ⟨h.output,fun z hz => ?_⟩
  have dif : z ≠ a := fun eq => hz (eq ▸ ha)
  simpa only [Store.write,Function.update_of_ne dif] using h.read z hz

end TargetedSamplers.Structured

end LogCostRAMFold

section HamiltonianRAMNeighborhood

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.TripleScan

open Multidigraph Classical

def arcScratch : Finset ℕ := {40,46,47,48,49}

def tailScratch := insert 43 (insert 50 arcScratch)

def weightScratch := insert 45 (insert 51 tailScratch)

def vertexScratch := insert 44 (insert 52 weightScratch)

theorem GraphView.frame {n m W base : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ}
    {s t : Fin n} {u v : Store} {regs : Finset ℕ} (g : GraphView (W := W) tail head w s t base u)
    (fr : Frame regs u v) (sub : regs ⊆ vertexScratch) : GraphView (W := W) tail head w s t base v := by
  have keep := fr.mono sub
  refine ⟨g.low,g.records.congr ?_,(keep.read 30 (by decide)).trans g.source,
    (keep.read 31 (by decide)).trans g.sink,(keep.read 32 (by decide)).trans g.zero,
    (keep.read 33 (by decide)).trans g.vertices,(keep.read 34 (by decide)).trans g.weights,
    (keep.read 35 (by decide)).trans g.table,(keep.read 41 (by decide)).trans g.stop,(keep.read 42 (by decide)).trans g.unit⟩
  intro a ha
  apply keep.read
  have := g.low
  simp only [vertexScratch,weightScratch,tailScratch,arcScratch,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem inspectArc_exec {τ : Tapes} {b n m W base : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ}
    (hw : ∀ e, w e ≤ W) {s t : Fin n} (q : ArcType (Fin n) W) (u : Store)
    (g : GraphView (W := W) tail head w s t base u) (tailWord : u.mem 43 = q.1.val)
    (headWord : u.mem 44 = q.2.1.val) (weightWord : u.mem 45 = q.2.2.val) (fit : u.Fits b) :
    ∃ z j, Exec τ (fun v => v.Fits b) inspectArc u z j ∧ j ≤ 18*m+15 ∧ Frame arcScratch u z ∧
      z.mem 46 = (if Multidigraph.retainArc (⟨tail,head⟩ : Multidigraph (Fin n) (Fin m)) w s t hw q then 1 else 0) := by
  let v := u.write 40 base
  have e : (Op.add 40 35 32).eval τ u = v := by simp [Op.eval,v,g.table,g.zero]
  have f : v.Fits b := Store.write_fits fit _ (g.table ▸ fit 35)
  have reset : Exec τ (fun st => st.Fits b) (.op (.add 40 35 32)) u v 1 := by
    simpa only [e] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) u (.add 40 35 32) (e ▸ f))
  have fr := (Frame.refl arcScratch u).write 40 (by decide) base
  have view := g.frame fr (by decide)
  have key : wanted arcRegs v = (q.1.val,q.2.1.val,q.2.2.val) :=
    Prod.ext ((fr.read 43 (by decide)).trans tailWord)
      (Prod.ext ((fr.read 44 (by decide)).trans headWord) ((fr.read 45 (by decide)).trans weightWord))
  obtain ⟨z,j,run,hj,bit,result,_,out,frame⟩ := retainedQuery_exec (τ := τ) tail head w hw s t q
    arcRegs 30 31 base v view.records (fun i => by change 40+i.val < base; have := i.isLt; have := g.low; omega)
    (by change v.mem 40 = base; simp [v,Store.write]) view.stop view.unit key view.source view.sink
    (by unfold untouched; decide) (by unfold untouched; decide) f
  change z.mem 46 ≤ 1 at bit
  change z.mem 46 = 1 ↔ _ at result
  refine ⟨z,_,reset.seq run,by omega,fr.trans ⟨out,?_⟩,?_⟩
  · intro a ha
    apply frame
    change a ≠ 40 ∧ a ≠ 46 ∧ a ≠ 47 ∧ a ≠ 48 ∧ a ≠ 49
    simpa [arcScratch] using ha
  · split
    · exact result.mpr (by assumption)
    · have hnot : z.mem 46 ≠ 1 := fun h => (by assumption : ¬Multidigraph.retainArc _ w s t hw q) (result.mp h)
      omega

/-- Membership of a weight in the normalized incoming list is witnessed by a retained tail. -/
theorem normalized_incoming_iff {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ)
    (hw : ∀ e, w e ≤ W) (s t v : Fin n) (b : Fin (W+1)) :
    b.val ∈ Multidigraph.incomingWeights (Multidigraph.normalizedGraph H w s t hw)
      (Multidigraph.normalizedWeight H w s t hw) v ↔ ∃ a : Fin n, Multidigraph.retainArc H w s t hw (a,v,b) := by
  simp only [Multidigraph.incomingWeights,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨e,he,eq⟩
    have hh : e.val.2.1 = v := he
    have hb : e.val.2.2 = b := Fin.ext eq
    have heq : e.val = (e.val.1,v,b) := Prod.ext rfl (Prod.ext hh hb)
    exact ⟨e.val.1,heq ▸ e.property⟩
  · rintro ⟨a,ha⟩
    let e : RetainedArc H w s t hw := ⟨(a,v,b),ha⟩
    exact ⟨e,rfl,rfl⟩

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMNeighborhood

section FiniteSampling

/-! Counting estimates for independent samples from finite sets. -/

namespace FiniteSampling

open scoped BigOperators

open Classical

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def mean (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

noncomputable def probability (p : α → Prop) : ℝ :=
  mean fun x => if p x then 1 else 0

theorem probability_eq (p : α → Prop) :
    probability p = ((Finset.univ.filter p).card : ℝ) / Fintype.card α := by
  simp [probability, mean]

theorem mean_mono {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (by positivity)

theorem mean_const [Nonempty α] (c : ℝ) : mean (fun _ : α => c) = c := by
  have h : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, h, mul_div_cancel_left₀]

theorem mean_sub (f g : α → ℝ) : mean (fun x => f x - g x) = mean f - mean g := by
  simp [mean, Finset.sum_sub_distrib, sub_div]

theorem mean_mul_left (c : ℝ) (f : α → ℝ) : mean (fun x => c * f x) = c * mean f := by
  simp [mean, ← Finset.mul_sum, mul_div_assoc]

theorem mean_sum (f : β → α → ℝ) :
    mean (fun x => ∑ j, f j x) = ∑ j, mean (f j) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

theorem probability_not [Nonempty α] (p : α → Prop) :
    probability (fun x => ¬ p x) = 1 - probability p := by
  unfold probability
  conv_rhs => lhs; rw [← mean_const (α := α) 1]
  rw [← mean_sub]
  apply congrArg mean
  funext x
  by_cases h : p x <;> simp [h]

theorem probability_union (p q : α → Prop) :
    probability (fun x => p x ∨ q x) ≤ probability p + probability q := by
  unfold probability
  unfold mean
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : p x <;> by_cases hq : q x <;> simp [hp, hq]

theorem probability_exists (p : β → α → Prop) :
    probability (fun x => ∃ j, p j x) ≤ ∑ j, probability (p j) := by
  unfold probability
  rw [← mean_sum]
  apply mean_mono
  intro x
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    simpa [hj] using (Finset.single_le_sum (f := fun k => if p k x then (1 : ℝ) else 0)
      (fun k _ => by split <;> norm_num) (Finset.mem_univ j))
  · exact Finset.sum_nonneg fun k _ => by split <;> norm_num

theorem probability_mono {p q : α → Prop} (h : ∀ x, p x → q x) :
    probability p ≤ probability q := by
  apply mean_mono
  intro x
  by_cases hp : p x
  · simp [hp, h x hp]
  · simp [hp]; split <;> norm_num

/-- The probability that all independent coordinates have the same property. -/
theorem probability_all (p : α → Prop) (m : ℕ) :
    probability (fun a : Fin m → α => ∀ j, p (a j)) = probability p ^ m := by
  rw [probability_eq, probability_eq]
  have he : (@Finset.filter (Fin m → α) (fun a => ∀ j, p (a j))
      (fun a => Classical.propDecidable _) Finset.univ) =
      Fintype.piFinset (fun _ : Fin m => Finset.univ.filter p) := by
    ext a
    simp [Fintype.mem_piFinset]
  erw [he]
  rw [Fintype.card_piFinset_const, Fintype.card_pi_const]
  push_cast
  rw [div_pow]

/-- Uniform averaging on a pair of independent coordinates. -/
theorem mean_prod (f : α → β → ℝ) :
    mean (fun z : α × β => f z.1 z.2) = mean (fun x => mean (f x)) := by
  simp only [mean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div, div_div]
  rw [mul_comm (Fintype.card β : ℝ)]

theorem probability_prod (p : α → β → Prop) :
    probability (fun z : α × β => p z.1 z.2) = mean (fun x => probability (p x)) := by
  exact mean_prod (fun x y => @ite ℝ (p x y) (Classical.propDecidable _) 1 0)

theorem mean_prod_swap (f : α → β → ℝ) :
    mean (fun x => mean (f x)) = mean (fun y => mean (fun x => f x y)) := by
  simp only [mean, ← Finset.sum_div, div_div]
  rw [Finset.sum_comm, mul_comm (Fintype.card β : ℝ)]

/-- A counting form of Markov's inequality; no independence is needed. -/
theorem markov (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) {c : ℝ} (hc : 0 < c) :
    probability (fun x => c < f x) ≤ mean f / c := by
  apply (le_div_iff₀ hc).2
  rw [mul_comm, probability, ← mean_mul_left]
  apply mean_mono
  intro x
  by_cases hx : c < f x
  · simpa [hx] using hx.le
  · simpa [hx] using hf x

/-- One block misses with probability at most one half if its expected hit count is at least one. -/
theorem miss_block {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {k : ℕ} (hk : 1 ≤ k * p) :
    (1 - p) ^ k ≤ 1 / 2 := by
  have hbern : 2 ≤ (1 + p) ^ k := by
    linarith [one_add_mul_le_pow (by linarith : -2 ≤ p) k]
  have hprod : ((1 - p) ^ k) * ((1 + p) ^ k) ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀ (mul_nonneg (by linarith) (by linarith))
    nlinarith [sq_nonneg p]
  nlinarith only [hprod, mul_nonneg (pow_nonneg (sub_nonneg.mpr hp') k) (sub_nonneg.mpr hbern)]

end FiniteSampling

end FiniteSampling

section EnumerationSampling

namespace FiniteSampling

open scoped BigOperators

open Classical

variable {R U X : Type*} [Fintype R] [Fintype U] [Fintype X] [Nonempty R] [Nonempty U]

/-- The work counter includes repeated occurrences. -/
def reports (family : R → U → Finset X) {m : ℕ} (r : R) (u : Fin m → U) : ℕ :=
  ∑ j, (family r (u j)).card

/-- The determinant sum only uses distinct sets. -/
noncomputable def covered (family : R → U → Finset X) {m : ℕ} (r : R) (u : Fin m → U) : Finset X :=
  Finset.univ.biUnion fun j => family r (u j)

omit [Fintype R] [Fintype X] [Nonempty R] in
private theorem miss_one (family : R → U → Finset X) (r : R) (x : X) (k n : ℕ)
    (hhit : 1 ≤ k * probability (fun u => x ∈ family r u)) :
    probability (fun a : Fin (k * (n + 4)) → U => ∀ j, x ∉ family r (a j)) ≤
      (1 / 2 : ℝ) ^ (n + 4) := by
  let p := fun u => x ∈ family r u
  change probability (fun a : Fin (k * (n + 4)) → U => ∀ j, ¬p (a j)) ≤ _
  rw [probability_all (fun u => ¬p u) _, probability_not p, pow_mul]
  have hlo : 0 ≤ probability p := by rw [probability_eq]; positivity
  have hhi : probability p ≤ 1 := by
    rw [probability_eq, div_le_one (by exact_mod_cast Fintype.card_pos (α := U))]
    exact_mod_cast (Finset.card_le_univ (@Finset.filter U p (fun a => Classical.propDecidable (p a)) Finset.univ))
  exact pow_le_pow_left₀ (pow_nonneg (sub_nonneg.mpr hhi) k) (miss_block hlo hhi hhit) _

omit [Fintype R] [Nonempty R] in
private theorem miss_any (family : R → U → Finset X) (live : R → Finset X) (r : R) (k n : ℕ)
    (hcard : Fintype.card X ≤ 2 ^ n)
    (hhit : ∀ x ∈ live r, 1 ≤ k * probability (fun u => x ∈ family r u)) :
    probability (fun a : Fin (k * (n + 4)) → U => ¬live r ⊆ covered family r a) ≤ 1 / 16 := by
  let p := fun (x : live r) (a : Fin (k * (n + 4)) → U) => ∀ j, x.1 ∉ family r (a j)
  calc
    _ ≤ probability (fun a => ∃ x, p x a) := by
      apply probability_mono
      intro a h
      by_contra! hn
      apply h
      intro x hx
      have hh := hn (⟨x, hx⟩ : live r)
      simpa [p, covered] using hh
    _ ≤ ∑ x : live r, probability (p x) := probability_exists p
    _ ≤ ∑ _x : live r, (1 / 2 : ℝ) ^ (n + 4) :=
      Finset.sum_le_sum fun x _ => miss_one family r x.1 k n (hhit x.1 x.2)
    _ = ((live r).card : ℝ) * (1 / 2 : ℝ) ^ (n + 4) := by simp
    _ ≤ (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ (n + 4) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (Finset.card_le_univ (live r)).trans hcard
    _ = 1 / 16 := by rw [pow_add, ← mul_assoc, ← mul_pow]; norm_num

/-- Coverage and a worst-case cutoff for fixed-length independent trials. The shared parameter
`r` is reused by every trial. Only the trials conditional on that parameter are independent. -/
theorem coverage_and_cutoff (family : R → U → Finset X) (live : R → Finset X) (k n : ℕ)
    (hk : 0 < k) (hcard : Fintype.card X ≤ 2 ^ n)
    (hhit : ∀ r x, x ∈ live r → 1 ≤ k * probability (fun u => x ∈ family r u))
    (hload : ∀ u, mean (fun r => ((family r u).card : ℝ)) ≤ 1) :
    let m := k * (n + 4)
    5 / 6 ≤ probability (fun z : R × (Fin m → U) =>
      live z.1 ⊆ covered family z.1 z.2 ∧ reports family z.1 z.2 ≤ 12 * m) := by
  let m := k * (n + 4)
  let A := Fin m → U
  let uncovered := fun z : R × A => ¬ live z.1 ⊆ covered family z.1 z.2
  let overflow := fun z : R × A => 12 * m < reports family z.1 z.2
  have hmiss : probability uncovered ≤ 1 / 16 := by
    dsimp only [uncovered]
    rw [probability_prod (fun (r : R) (a : A) => ¬live r ⊆ covered family r a)]
    exact (mean_mono fun r => miss_any family live r k n hcard (hhit r)).trans_eq (mean_const _)
  have hexp : mean (fun z : R × A => (reports family z.1 z.2 : ℝ)) ≤ m := by
    change mean (fun z : R × A => (fun r a => (reports family r a : ℝ)) z.1 z.2) ≤ _
    let f := fun (r : R) (a : A) => (reports family r a : ℝ)
    rw [mean_prod f, mean_prod_swap f]
    dsimp only [f]
    apply le_trans _ (mean_const (α := A) (m : ℝ)).le
    apply mean_mono
    intro a
    simp only [reports, Nat.cast_sum, mean_sum]
    calc
      _ ≤ ∑ _j : Fin m, (1 : ℝ) := Finset.sum_le_sum fun j _ => hload (a j)
      _ = _ := by simp
  have hm : (0 : ℝ) < m := by dsimp [m]; positivity
  have hover : probability overflow ≤ 1 / 12 := by
    have hc : (0 : ℝ) < 12 * m := by positivity
    calc
      _ = probability (fun z : R × A => (12 : ℝ) * m < (reports family z.1 z.2 : ℝ)) := by
        apply congrArg probability; funext z; apply propext
        change 12 * m < reports family z.1 z.2 ↔ _
        exact_mod_cast Iff.rfl
      _ ≤ _ := markov _ (fun _ => by positivity) hc
      _ ≤ 1 / 12 := by apply (div_le_iff₀ hc).2; linarith
  have hbad := (probability_union uncovered overflow).trans (add_le_add hmiss hover)
  have hcompl := probability_not (fun z : R × A => uncovered z ∨ overflow z)
  have he : (fun z : R × A => ¬ (uncovered z ∨ overflow z)) =
      (fun z : R × A => live z.1 ⊆ covered family z.1 z.2 ∧ reports family z.1 z.2 ≤ 12 * m) := by
    funext z
    simp [uncovered, overflow]
  rw [he] at hcompl
  change 5 / 6 ≤ probability (fun z : R × A =>
    live z.1 ⊆ covered family z.1 z.2 ∧ reports family z.1 z.2 ≤ 12 * m)
  linarith

end FiniteSampling

end EnumerationSampling

section DyadicSampling

namespace FiniteSampling

open Classical

variable {A U X : Type*}

@[simp] theorem padded_code (code : A ↪ U) (family : A → Finset X) (a : A) :
    padded code family (code a) = family a := by
  have h : ∃ v, code v = code a := ⟨a, rfl⟩
  simp only [padded, dif_pos h, code.injective h.choose_spec]

theorem padded_empty (code : A ↪ U) (family : A → Finset X) {u : U}
    (h : ¬∃ a, code a = u) : padded code family u = ∅ := by simp [padded, h]

variable [Fintype A] [Fintype U]

private theorem padded_hits (code : A ↪ U) (family : A → Finset X) (x : X) :
    (@Finset.filter U (fun u => x ∈ padded code family u) (fun _ => Classical.propDecidable _) Finset.univ).card =
      (@Finset.filter A (fun a => x ∈ family a) (fun _ => Classical.propDecidable _) Finset.univ).card := by
  calc
    _ = ((@Finset.filter A (fun a => x ∈ family a) (fun _ => Classical.propDecidable _) Finset.univ).map code).card := by
      congr 1
      ext u
      by_cases h : ∃ a, code a = u
      · obtain ⟨a, rfl⟩ := h
        simp
      · simp [padded_empty _ _ h, Finset.mem_map]
        exact fun a _ => fun ha => h ⟨a, ha⟩
    _ = _ := Finset.card_map _

/-- Using an alphabet at most twice as large loses at most a factor two per whole trial. -/
theorem padded_hit_lower [Nonempty A] [Nonempty U] (code : A ↪ U) (family : A → Finset X)
    (hwidth : Fintype.card U ≤ 2 * Fintype.card A) (x : X) :
    probability (fun a => x ∈ family a) ≤ 2 * probability (fun u => x ∈ padded code family u) := by
  simp only [probability_eq]
  rw [padded_hits, ← mul_div_assoc]
  apply (div_le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := A))
    (by exact_mod_cast Fintype.card_pos (α := U))).2
  have hw : (Fintype.card U : ℝ) ≤ 2 * Fintype.card A := by exact_mod_cast hwidth
  have h := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg (α := ℝ)
    (@Finset.filter A (fun a => x ∈ family a) (fun _ => Classical.propDecidable _) Finset.univ).card)
  linarith only [h]

theorem coinBlock_bounds (A : Type*) [Fintype A] [Nonempty A] :
    Fintype.card A ≤ Fintype.card (CoinBlock A) ∧
      Fintype.card (CoinBlock A) ≤ 2 * Fintype.card A := by
  simp only [CoinBlock, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  let N := Fintype.card A
  change N ≤ 2 ^ Nat.clog 2 N ∧ 2 ^ Nat.clog 2 N ≤ 2 * N
  refine ⟨Nat.le_pow_clog (by decide) _, ?_⟩
  have hn : 0 < N := Fintype.card_pos
  by_cases h : 1 < N
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.clog_pos (by decide : 1 < 2) h).ne'
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) h
    rw [hj] at hp ⊢
    simp only [Nat.pred_succ] at hp
    rw [pow_succ]
    omega
  · have he : N = 1 := by omega
    simp [he]

end FiniteSampling

end DyadicSampling

section HamiltonianParitySampling

namespace DirectedHamiltonicity.Main.Multidigraph

open FiniteSampling Classical

open scoped BigOperators

theorem samplingBlockSize_bounds (n d : ℕ) :
    let b := (2 - (1 / 2 : ℝ) ^ d) ^ (n - 2)
    2 * b ≤ samplingBlockSize n d ∧ (samplingBlockSize n d : ℝ) ≤ 4 * b := by
  dsimp only
  let q := (2 - (1 / 2 : ℚ) ^ d) ^ (n - 2)
  have hq : 1 ≤ q := by
    apply one_le_pow₀
    have h := pow_le_one₀ (by norm_num : (0 : ℚ) ≤ 1/2) (by norm_num : (1/2 : ℚ) ≤ 1) (n := d)
    linarith
  have lower := Nat.le_ceil q
  have upper := Nat.ceil_lt_add_one (zero_le_one.trans hq)
  have hqr : (q : ℝ) = (2 - (1/2 : ℝ)^d) ^ (n-2) := by
    simp [q, Rat.cast_pow, Rat.cast_sub]
  rw [← hqr]
  change 2 * (q : ℝ) ≤ ((2 * ⌈q⌉₊ : ℕ) : ℝ) ∧ ((2 * ⌈q⌉₊ : ℕ) : ℝ) ≤ 4 * (q : ℝ)
  push_cast
  constructor
  · exact_mod_cast (show (2:ℚ) * q ≤ 2 * ⌈q⌉₊ by linarith)
  · exact_mod_cast (show (2:ℚ) * ⌈q⌉₊ ≤ 4 * q by linarith)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
private theorem coeffs_nonempty : Nonempty (H.NonzeroCoeffs w s t) := by
  refine ⟨fun i => ⟨fun j => if j = none then 1 else 0, ?_⟩⟩
  intro h
  have hh := congrFun h none
  simp at hh

omit [DecidableEq V] [DecidableEq E] in
theorem samplingDegree_le {d : ℕ} (hd : 1 ≤ d) (hw : ∀ v, (H.incomingWeights w v).card ≤ d) :
    H.samplingDegree w ≤ d := max_le hd (Finset.sup_le fun v _ => hw v)

/-- For a normalized instance, independent fixed-length fair-bit blocks enumerate every
survivor and issue at most twelve times as many reports as there are trials, with probability at least 5/6.
The first random mask is shared across the trials. -/
theorem parity_coverage_probability (hst : s ≠ t) (hn : H.IsNormalized w s t)
    (code : H.NonzeroCoeffs w s t ↪ CoinBlock (H.NonzeroCoeffs w s t)) :
    let k := samplingBlockSize (Fintype.card V) (H.samplingDegree w)
    let m := k * (Fintype.card V + 4)
    5 / 6 ≤ probability (fun z : H.RandomMasks w s t × (Fin m → CoinBlock (H.NonzeroCoeffs w s t)) =>
      H.survivors w s t z.1 ⊆ covered (H.coinFamily w s t code) z.1 z.2 ∧
      reports (H.coinFamily w s t code) z.1 z.2 ≤ 12 * m) := by
  classical
  let _ := coeffs_nonempty H w s t
  let n := Fintype.card V
  let d := H.samplingDegree w
  let b := (2 - (1 / 2 : ℝ)^d) ^ (n - 2)
  let k := samplingBlockSize n d
  have hb : 1 ≤ b := by
    apply one_le_pow₀
    have h := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1) (n := d)
    linarith
  have hlow : 2 * b ≤ k := (samplingBlockSize_bounds n d).1
  have hk : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
  apply coverage_and_cutoff (H.coinFamily w s t code) (H.survivors w s t) k n hk
  · rw [Fintype.card_finset]
    exact Nat.pow_le_pow_right (by decide) (Fintype.card_subtype_le _)
  · intro r x hx
    have hd : 1 ≤ d := le_max_left .. 
    have hd' (v : V) : (H.incomingWeights w v).card ≤ d :=
      (Finset.le_sup (f := fun v => (H.incomingWeights w v).card) (Finset.mem_univ v)).trans (le_max_right ..)
    let f := fun a : H.NonzeroCoeffs w s t => H.sampled w s t (fun i => (a i).1) r
    obtain ⟨hprob, hbound⟩ := DirectedHamiltonicity.Main.lemma9 H w s t hst hn d hd hd' r x hx
    have h₁ : b⁻¹ ≤ probability (fun a => x ∈ f a) := by
      apply hbound.trans_eq
      rw [← hprob, probability_eq]
      apply congrArg (fun Z : Finset (H.NonzeroCoeffs w s t) =>
        (Z.card : ℝ) / Fintype.card (H.NonzeroCoeffs w s t))
      ext a
      simp [f]
    have h₂ := padded_hit_lower code f (coinBlock_bounds (H.NonzeroCoeffs w s t)).2 x
    let p := probability (fun u => x ∈ padded code f u)
    have hp : 0 ≤ p := by dsimp [p]; rw [probability_eq]; positivity
    have hbp : 1 ≤ (2 * p) * b := (div_le_iff₀ (by linarith : 0 < b)).1 (by
      simpa [one_div, p] using h₁.trans h₂)
    change 1 ≤ (k : ℝ) * p
    nlinarith only [hbp, mul_nonneg (sub_nonneg.mpr hlow) hp]
  · intro u
    by_cases he : ∃ a, code a = u
    · obtain ⟨a, rfl⟩ := he
      simpa only [coinFamily, padded_code, mean] using
        (DirectedHamiltonicity.Main.lemma10 H w s t hst hn a).le
    · simp only [coinFamily, padded_empty _ _ he, Finset.card_empty, Nat.cast_zero]
      rw [mean_const]
      norm_num

omit [DecidableEq V] [DecidableEq E] in
/-- The graph supplies its own exponent parameter; every larger valid bound dominates the
number of trials. The polynomial factor has no dependence on the supplied degree. -/
theorem parity_trials_le (d : ℕ) (hd : 1 ≤ d) (hdeg : ∀ v, (H.incomingWeights w v).card ≤ d) :
    let n := Fintype.card V
    ((samplingBlockSize n (H.samplingDegree w) * (n + 4) : ℕ) : ℝ) ≤
      4 * (n + 4 : ℕ) * (2 - (1 / 2 : ℝ)^d)^n := by
  let n := Fintype.card V
  let D := H.samplingDegree w
  have hD : D ≤ d := H.samplingDegree_le w hd hdeg
  have hhalf (j : ℕ) : (1/2 : ℝ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hone : 1 ≤ 2 - (1/2 : ℝ)^d := by linarith [hhalf d]
  have hlo : 0 ≤ 2 - (1/2 : ℝ)^D := by linarith [hhalf D]
  have hbase : 2 - (1/2 : ℝ)^D ≤ 2 - (1/2 : ℝ)^d :=
    sub_le_sub_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hD) _
  have hp : (2 - (1/2 : ℝ)^D)^(n-2) ≤ (2 - (1/2 : ℝ)^d)^n :=
    (pow_le_pow_left₀ hlo hbase _).trans (pow_le_pow_right₀ hone (Nat.sub_le ..))
  have hs := (samplingBlockSize_bounds n D).2
  change ((samplingBlockSize n D * (n + 4) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_mul]
  calc
    _ ≤ (4 * (2 - (1/2 : ℝ)^d)^n) * ((n + 4 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (hs.trans (mul_le_mul_of_nonneg_left hp (by norm_num))) (by positivity)
    _ = _ := by ring

omit [DecidableEq E] in
/-- All the coefficients of one trial can be indexed by a polynomial number of bits, even
when there are exponentially many possible tuples. -/
theorem coefficient_block_width :
    Nat.clog 2 (Fintype.card (H.NonzeroCoeffs w s t)) ≤
      Fintype.card V * (Fintype.card E + 1) := by
  classical
  apply Nat.clog_le_of_le_pow
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _i : Internal s t, 2 ^ (Fintype.card E + 1) := by
      apply Finset.prod_le_prod'
      intro i _
      have hc := Fintype.card_subtype_le (fun a : H.CoeffVec w i.1 => a ≠ 0)
      change _ ≤ _ at hc
      have hw : (H.incomingWeights w i.1).card ≤ Fintype.card E :=
        Finset.card_image_le.trans (Finset.card_le_univ _)
      have he : Fintype.card (H.CoeffVec w i.1) = 2 ^ ((H.incomingWeights w i.1).card + 1) := by
        simp [CoeffVec, ZMod.card]
      exact hc.trans (he.le.trans (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ hw)))
    _ = 2 ^ (Fintype.card (Internal s t) * (Fintype.card E + 1)) := by
      simp [pow_mul, Nat.mul_comm]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Fintype.card_subtype_le _))

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianParitySampling

section HamiltonianIntegerSchedule

namespace DirectedHamiltonicity.Main.Multidigraph

def trialNumerator (n d : ℕ) := (2^(d+1)-1)^(n-2)

def trialDenominator (n d : ℕ) := (2^d)^(n-2)

/-- The exact sample count uses only natural arithmetic and a positive integer divisor. -/
def integerBlockSize (n d : ℕ) :=
  2*((trialNumerator n d+trialDenominator n d-1)/trialDenominator n d)

private theorem ceil_ratio (a b : ℕ) (hb : 0 < b) : ⌈(a:ℚ)/(b:ℚ)⌉₊ = (a+b-1)/b := by
  rw [← Nat.ceilDiv_eq_add_pred_div]
  have test (c : ℕ) : ⌈(a:ℚ)/(b:ℚ)⌉₊ ≤ c ↔ a ⌈/⌉ b ≤ c := by
    rw [Nat.ceil_le,div_le_iff₀ (by exact_mod_cast hb : 0 < (b:ℚ)),ceilDiv_le_iff_le_mul hb,mul_comm b c]
    exact_mod_cast (Iff.rfl : a ≤ c*b ↔ a ≤ c*b)
  exact le_antisymm ((test _).2 le_rfl) ((test _).1 le_rfl)

theorem integerBlockSize_eq (n d : ℕ) : integerBlockSize n d = samplingBlockSize n d := by
  have den : 0 < trialDenominator n d := by dsimp [trialDenominator]; positivity
  have power : 2-(1/2:ℚ)^d = ((2^(d+1)-1 : ℕ):ℚ)/(2^d : ℕ) := by
    rw [Nat.cast_sub (Nat.one_le_two_pow (n := d+1))]
    push_cast
    rw [div_pow,one_pow,pow_succ]
    field_simp
  have ratio : (2-(1/2:ℚ)^d)^(n-2) = (trialNumerator n d:ℚ)/(trialDenominator n d:ℚ) := by
    rw [power,div_pow]
    simp only [trialNumerator,trialDenominator,Nat.cast_pow]
  rw [samplingBlockSize,ratio,ceil_ratio _ _ den]
  rfl

/-- Even the doubled dividend used by binary division has polynomially many bits.
This includes the zero exponent and does not rely on the value of the target weight. -/
theorem schedule_word_sizes (n d : ℕ) :
    let e := (d+1)*(n-2)
    let a := trialNumerator n d
    let b := trialDenominator n d
    a.size ≤ e+1 ∧ b.size ≤ e+1 ∧ (2*(a+b-1)+2).size ≤ e+3 := by
  intro e a b
  have ha : a ≤ 2^e := by
    rw [show 2^e = (2^(d+1))^(n-2) by rw [← pow_mul]]
    exact Nat.pow_le_pow_left (Nat.sub_le _ _) _
  have hb : b ≤ 2^e := by
    change (2^d)^(n-2) ≤ 2^((d+1)*(n-2))
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_succ d))
  have pos : 0 < 2^e := pow_pos (by decide) _
  have p₁ : 2^(e+1) = 2*2^e := by rw [pow_succ,Nat.mul_comm]
  have p₃ : 2^(e+3) = 8*2^e := by rw [pow_add]; ring
  refine ⟨Nat.size_le.mpr (by rw [p₁]; omega),Nat.size_le.mpr (by rw [p₁]; omega),
    Nat.size_le.mpr (by rw [p₃]; omega)⟩

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianIntegerSchedule

section LogCostRAMArithmetic

namespace TargetedSamplers.Structured.Word

theorem size_mul_le_add (x y : ℕ) : (x*y).size ≤ x.size+y.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left x (Nat.lt_size_self y).le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self x) (pow_pos (by decide) _))

end TargetedSamplers.Structured.Word

end LogCostRAMArithmetic

section HamiltonianRAMSchedule

namespace DirectedHamiltonicity.Main.Multidigraph

open TargetedSamplers.Structured TargetedSamplers.Structured.Word

/-- The exponential-valued trial count is constructed in polynomial preliminary time. -/
theorem schedule_polynomial (n d : ℕ) :
    let S := n+d+2
    scheduleWidth n d ≤ 18*S^2 ∧ scheduleSteps n d ≤ 40000*S^5 := by
  intro S
  let w := scheduleWidth n d
  have pos : 1 ≤ S := by dsimp [S]; omega
  have ns : n ≤ S := by dsimp [S]; omega
  have ds : d+1 ≤ S := by dsimp [S]; omega
  have qs : n-2 ≤ S := by omega
  have ss : S ≤ S^2 := by simpa [pow_two] using Nat.mul_le_mul_left S pos
  have ss' : 1 ≤ S^2 := pos.trans ss
  have deg := Nat.mul_le_mul ds qs
  have word : w ≤ 18*S^2 := by
    dsimp [w,scheduleWidth]
    have joint : n+d ≤ S := by dsimp [S]; omega
    nlinarith only [deg,joint,ss,ss']
  have quad := Nat.mul_le_mul word (show 5*w+9 ≤ 99*S^2 by omega)
  have fourth : 1 ≤ S^4 := Nat.succ_le_of_lt (pow_pos pos 4)
  have per : w*(5*w+9)+15 ≤ 1800*S^4 := by nlinarith only [quad,fourth]
  have calls : d+2*(n-2)+15 ≤ 18*S := by omega
  refine ⟨word,(Nat.mul_le_mul calls per).trans ?_⟩
  nlinarith only [Nat.zero_le (S^5)]

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianRAMSchedule

section HamiltonianRAMDenseEntry

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.TripleScan Multidigraph Classical

/-- Address of a weighted triple in the dense normalized cache. -/
def gridOffset {n W : ℕ} (a v : Fin n) (k : Fin (W+1)) : ℕ :=
  (a.val*n+v.val)*(W+1)+k.val

theorem gridOffset_bound {n W : ℕ} (a v : Fin n) (k : Fin (W+1)) :
    gridOffset a v k < n*(n*(W+1)) := by
  have vh := v.isLt
  have kh := k.isLt
  have row := Nat.mul_le_mul_right n (Nat.succ_le_of_lt a.isLt)
  have pre : a.val*n+v.val < n*n := by rw [Nat.succ_mul] at row; omega
  have block := Nat.mul_le_mul_right (W+1) (Nat.succ_le_of_lt pre)
  rw [Nat.succ_mul,Nat.mul_assoc] at block
  dsimp [gridOffset]; omega

theorem linearArc_gridOffset {n W : ℕ} (a v : Fin n) (k : Fin (W+1)) :
    linearArc (Nat.zero_lt_of_lt a.isLt) (gridOffset a v k) (gridOffset_bound a v k) = (a,v,k) := by
  have hn : 0 < n := Nat.zero_lt_of_lt a.isLt
  have hw : 0 < W+1 := Nat.succ_pos _
  have within : v.val*(W+1)+k.val < n*(W+1) := by
    have step := Nat.mul_le_mul_right (W+1) (Nat.succ_le_of_lt v.isLt)
    rw [Nat.succ_mul] at step
    have hk := k.isLt
    omega
  have row : gridOffset a v k/(n*(W+1))=a.val := by
    rw [show gridOffset a v k = (v.val*(W+1)+k.val)+a.val*(n*(W+1)) by unfold gridOffset; ring,
      Nat.add_mul_div_right _ _ (Nat.mul_pos hn hw),Nat.div_eq_of_lt within,Nat.zero_add]
  have block : gridOffset a v k/(W+1)=a.val*n+v.val := by
    rw [gridOffset,Nat.add_comm,Nat.add_mul_div_right _ _ hw,Nat.div_eq_of_lt k.isLt,Nat.zero_add]
  exact Prod.ext (Fin.ext row) (Prod.ext (Fin.ext (by
    simp only [linearArc,block,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt v.isLt])) (Fin.ext (by
    simp only [linearArc,gridOffset,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt k.isLt])))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMDenseEntry

section PackedBinaryStacks

namespace TargetedSamplers.Structured.BinaryStack

open Word

@[simp] theorem packed_nil : packed [] = 1 := rfl

theorem packed_cons (b : Bool) (xs : List Bool) : packed (b::xs) = packed xs+packed xs+b.toNat := by
  cases b <;> simp [packed,Nat.bit,two_mul]

theorem packed_pos (xs : List Bool) : 0 < packed xs := by
  induction xs with
  | nil => decide
  | cons b xs ih => rw [packed_cons]; omega

@[simp] theorem packed_size (xs : List Bool) : (packed xs).size = xs.length+1 := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    change (Nat.bit b (packed xs)).size = _
    rw [Nat.size_bit (Nat.ne_of_gt (packed_pos (b::xs))),ih,List.length_cons]

/-- Bits below the high sentinel are the numbered coordinates of the subset. -/
theorem packed_testBit (xs : List Bool) (i : ℕ) (hi : i < xs.length) : (packed xs).testBit i = xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => exact Nat.testBit_bit_zero b (packed bs)
    | succ i => simpa only [packed,Nat.testBit_bit_succ,List.getElem_cons_succ] using ih i (by simpa using hi)

end TargetedSamplers.Structured.BinaryStack

end PackedBinaryStacks

section HamiltonianAdjacencyBits

namespace DirectedHamiltonicity.Main.NativeGraph

open Multidigraph InputRAM Classical TargetedSamplers.Structured.BinaryStack

variable {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ) (hw : ∀ e, w e ≤ W) (s t : Fin n)

@[simp] theorem adjacencyBits_length : (adjacencyBits H w hw s t).length=n*(n*(W+1)) := by simp [adjacencyBits]

theorem adjacencyBits_testBit (a v : Fin n) (k : Fin (W+1)) :
    (packed (adjacencyBits H w hw s t)).testBit (gridOffset a v k)=decide (H.retainArc w s t hw (a,v,k)) := by
  rw [packed_testBit _ _ (by simpa using gridOffset_bound a v k)]
  simp only [adjacencyBits,List.getElem_ofFn,linearArc_gridOffset]

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianAdjacencyBits

section HamiltonianRequestWidth

namespace DirectedHamiltonicity.Main.InputRAM

theorem argumentWidth_room (n h : ℕ) :
    let N := n*(n*h)
    N+1 ≤ argumentWidth n h ∧ n*(N+1)+1 ≤ argumentWidth n h ∧ n+h+8 ≤ argumentWidth n h := by
  intro N
  simp only [argumentWidth,Nat.succ_mul]
  dsimp [N]
  omega

theorem argumentWidth_le (n m W : ℕ) :
    argumentWidth n (W+1) ≤ 24*(n+m+W+3)^4 := by
  let S := n+m+W+3
  have hn : n ≤ S := by dsimp [S];omega
  have hn' : n+1 ≤ S := by dsimp [S];omega
  have wh : W+1 ≤ S := by dsimp [S];omega
  have pos : 1 ≤ S := by dsimp [S];omega
  have N : n*(n*(W+1)) ≤ S*(S*S) := Nat.mul_le_mul hn (Nat.mul_le_mul hn wh)
  have amp := Nat.mul_le_mul hn' (Nat.add_le_add_right N 1)
  have hS : S ≤ S^4 := by simpa only [pow_one] using Nat.pow_le_pow_right pos (by decide : 1 ≤ 4)
  change (n+1)*(n*(n*(W+1))+1)+n+(W+1)+16 ≤ 24*S^4
  nlinarith only [amp,hn,wh,hS,pos]

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRequestWidth

section RankedCoinSampling

/-! Explicit ranks for tuples of nonzero binary words, and fixed-length fair-bit decoding. -/

namespace FiniteSampling

open scoped BigOperators

/-- Extract a row by division by the product of its predecessors and reduction modulo its radix. -/
theorem tupleRank_digit {I : Type*} {k : ℕ} {A : I → Type*} (order : I ≃ Fin k)
    (radix : I → ℕ) (row : ∀ i, A i ≃ Fin (radix i))
    (z : Fin (∏ j : Fin k, radix (order.symm j))) (j : Fin k) :
    (row (order.symm j) ((tupleRank order radix row).symm z (order.symm j))).val =
      (z.val / (∏ h : Fin j.val, radix (order.symm (Fin.castLE j.isLt.le h)))) % radix (order.symm j) := by
  let a := (tupleRank order radix row).symm z
  let digit := fun i : Fin k => row (order.symm i) (a (order.symm i))
  have hz : finPiFinEquiv digit = z := (tupleRank order radix row).apply_symm_apply z
  have hd := congrArg (fun x => (finPiFinEquiv (n := fun i => radix (order.symm i))).symm x j) hz
  simp only [Equiv.symm_apply_apply] at hd
  exact congrArg Fin.val hd

/-- The leading constant coordinate and every weight coordinate are bits of one plus the row digit. -/
theorem nonzeroRowRank_bit {I : Type*} {k : ℕ} (cols : I ≃ Fin k) (z : Fin (2^k-1)) (i : I) :
    (((nonzeroRowRank cols).symm z).val i).val = ((z.val+1)/2^(cols i).val)%2 := rfl

variable {A : Type*} [Fintype A] {N : ℕ}

/-- Convert a known arithmetic rank into the injection used by the sampling theorem. -/
def rankedCode (rank : A ≃ Fin N) : A ↪ CoinBlock A :=
  let width := Nat.clog 2 (Fintype.card A)
  let h : N ≤ 2^width := by
    have hc := Fintype.card_congr rank
    rw [Fintype.card_fin] at hc
    exact hc ▸ Nat.le_pow_clog (by decide) (Fintype.card A)
  { toFun := fun x => (binaryRank width).symm (Fin.castLE h (rank x))
    inj' := by
      intro x y hxy
      apply rank.injective
      apply Fin.ext
      exact congrArg (fun u : Fin (2^width) => u.val) ((binaryRank width).symm.injective hxy) }

@[simp] theorem rankedCode_value (rank : A ≃ Fin N) (x : A) :
    (binaryRank _ (rankedCode rank x)).val = (rank x).val := by
  change ((binaryRank _) ((binaryRank _).symm _)).val = _
  simp

@[simp] theorem decodeRank_code (rank : A ≃ Fin N) (x : A) :
    decodeRank rank (rankedCode rank x) = some x := by
  simp [decodeRank, (rank x).isLt]

theorem rankedCode_of_decode {rank : A ≃ Fin N} {bits : CoinBlock A} {x : A}
    (h : decodeRank rank bits = some x) : rankedCode rank x = bits := by
  dsimp only [decodeRank] at h
  split at h
  · cases Option.some.inj h
    apply (binaryRank _).injective
    apply Fin.ext
    simp
  · contradiction

/-- The padded trial in the probability analysis agrees pointwise with an arithmetic decoder. -/
theorem padded_eq_decode {X : Type*} (rank : A ≃ Fin N) (family : A → Finset X) (bits : CoinBlock A) :
    padded (rankedCode rank) family bits = (decodeRank rank bits).elim ∅ family := by
  cases he : decodeRank rank bits with
  | none =>
    rw [padded_empty]
    · rfl
    rintro ⟨x, rfl⟩
    simp at he
  | some x =>
    have h := rankedCode_of_decode he
    rw [← h, padded_code]
    rfl

end FiniteSampling

end RankedCoinSampling

section FiniteCoinTape

namespace FiniteSampling

open Classical

variable {A B : Type*} [Fintype A] [Fintype B]

theorem probability_equiv (e : A ≃ B) (p : B → Prop) :
    probability (fun a => p (e a)) = probability p := by
  unfold probability mean
  rw [Fintype.card_congr e]
  congr 1
  exact e.sum_comp (fun b => @ite ℝ (p b) (Classical.propDecidable _) 1 0)

/-- A property of a fixed prefix has the same probability on every longer uniform tape. -/
theorem probability_prefix {r length : ℕ} (h : r ≤ length) (p : (Fin r → Bool) → Prop) :
    probability (fun c : Fin length → Bool => p (fun i => c (Fin.castLE h i))) = probability p := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
  let e := splitCoins r extra
  have he := probability_equiv e (fun z => p z.1)
  have h₁ : probability (fun z : (Fin r → Bool) × (Fin extra → Bool) => p z.1) = probability p := by
    rw [probability_prod (fun x _ => p x)]
    unfold probability
    congr 1
    funext x
    exact mean_const _
  exact he.trans h₁

end FiniteSampling

end FiniteCoinTape

section RAMRankedCoins

namespace FiniteSampling

open TargetedSamplers TargetedSamplers.Structured

open scoped BigOperators

/-- The external random tape places trial blocks consecutively after the shared mask. -/
theorem trialBlocks_at (prefixLen trials width : ℕ) (coins : List Bool) (i : Fin trials) (j : Fin width) :
    (trialBlocks trials width ((splitCoins prefixLen (trials*width)
      (fun k => coins[k.val]?.getD false)).2)) i j =
      coins[prefixLen+width*i.val+j.val]?.getD false := by
  change coins[prefixLen+(j.val+width*i.val)]?.getD false = _
  rw [show prefixLen+(j.val+width*i.val) = prefixLen+width*i.val+j.val by omega]

end FiniteSampling

end RAMRankedCoins

section BoundedEnumeration

/-! Output-sensitive enumeration from a binary prefix-feasibility test. -/

namespace BoundedEnumeration

/-- A specification of all accepted completions. The prefix is stored in reverse order. -/
def completions (accept : List Bool → Bool) : ℕ → List Bool → List (List Bool)
  | 0, pref => if accept pref then [pref] else []
  | k + 1, pref => completions accept k (false :: pref) ++ completions accept k (true :: pref)

/-- At a node with k unassigned bits, exactly the last positions of a returned word
are fixed. In particular a complete word is reported at most once. -/
theorem mem_completions (accept : List Bool → Bool) (k : ℕ) (pref xs : List Bool) :
    xs ∈ completions accept k pref ↔ xs.length = k+pref.length ∧ xs.drop k = pref ∧ accept xs = true := by
  induction k generalizing pref with
  | zero =>
    by_cases h : accept pref = true
    · simp [completions, h]
      constructor
      · rintro rfl
        exact ⟨rfl,rfl,h⟩
      · exact fun h => h.2.1
    · simp [completions, h]
      rintro _ rfl
      simpa using h
  | succ k ih =>
    simp only [completions, List.mem_append, ih, List.length_cons]
    have dropNext : xs.drop (k+1) = (xs.drop k).drop 1 := by simp
    constructor
    · rintro (⟨hlen,hd,ha⟩ | ⟨hlen,hd,ha⟩)
      all_goals exact ⟨by omega, by simp [dropNext,hd],ha⟩
    · rintro ⟨hlen,hd,ha⟩
      have hp : 0 < (xs.drop k).length := by simp; omega
      cases hx : xs.drop k with
      | nil => simp [hx] at hp
      | cons b tail =>
        have ht : tail = pref := by simpa [dropNext,hx] using hd
        subst tail
        cases b with
        | false => exact Or.inl ⟨by omega,rfl,ha⟩
        | true => exact Or.inr ⟨by omega,rfl,ha⟩

theorem completions_nodup (accept : List Bool → Bool) (k : ℕ) (pref : List Bool) :
    (completions accept k pref).Nodup := by
  induction k generalizing pref with
  | zero => simp only [completions]; split <;> simp
  | succ k ih =>
    refine List.nodup_append.mpr ⟨ih _, ih _, ?_⟩
    rintro x hx y hy rfl
    have h₁ := ((mem_completions accept k _ x).mp hx).2.1
    have h₂ := ((mem_completions accept k _ x).mp hy).2.1
    simp [h₁] at h₂

variable (accept : List Bool → Bool) (viable : ℕ → List Bool → Bool)

variable (tests : ∀ k pref, viable k pref = true ↔ (completions accept k pref).length > 0)

include tests in
theorem search_words (k : ℕ) (pref : List Bool) (cap : ℕ) :
    (search viable k pref cap).words = (completions accept k pref).take cap := by
  induction k generalizing pref cap with
  | zero =>
      cases cap with
      | zero => rfl
      | succ cap =>
        have hv := tests 0 pref
        cases ha : accept pref <;> simp [completions, ha] at hv <;>
          simp [search, completions, ha, hv]
  | succ k ih =>
      cases cap with
      | zero => rfl
      | succ cap =>
        by_cases hv : viable (k+1) pref = true
        · simp only [search, hv, if_true, ih, List.length_take, completions, List.take_append]
          congr 2
          omega
        · have hz : completions accept (k+1) pref = [] := by
            apply List.eq_nil_of_length_eq_zero
            have := mt (tests _ _).mpr hv
            omega
          simp [search, hv, hz]

include tests in
theorem search_probes (k : ℕ) (pref : List Bool) (cap : ℕ) :
    let out := search viable k pref cap
    out.probes ≤ 1 + 2 * k * out.words.length := by
  induction k generalizing pref cap with
  | zero =>
    cases cap with
    | zero => simp [search]
    | succ cap => cases hv : viable 0 pref <;> simp [search, hv]
  | succ k ih =>
    cases cap with
    | zero => simp [search]
    | succ cap =>
      by_cases hv : viable (k+1) pref = true
      · let left := search viable k (false :: pref) (cap+1)
        let right := search viable k (true :: pref) (cap+1-left.words.length)
        have hpos : 0 < (search viable (k+1) pref (cap+1)).words.length := by
          rw [search_words accept viable tests, List.length_take]
          exact lt_min (Nat.succ_pos _) ((tests _ _).mp hv)
        have he : search viable (k+1) pref (cap+1) =
            ⟨left.words ++ right.words, 1 + left.probes + right.probes⟩ := by simp [search, hv, left, right]
        rw [he]
        rw [he, List.length_append] at hpos
        simp only [List.length_append]
        have hl : left.probes ≤ 1 + 2 * k * left.words.length := ih _ _
        have hr : right.probes ≤ 1 + 2 * k * right.words.length := ih _ _
        nlinarith
      · simp [search, hv]

end BoundedEnumeration

end BoundedEnumeration

section AffinePrefixEnumeration

/-! Output-sensitive enumeration of affine Boolean systems using the registered Gaussian counter. -/

namespace AffinePrefixEnumeration

open EditGV897.Main BoundedEnumeration

def wordBits {n : ℕ} (x : Word n) : List Bool := List.ofFn fun i => finTwoEquiv (x i)

@[simp] theorem length_wordBits {n : ℕ} (x : Word n) : (wordBits x).length = n := by simp [wordBits]

@[simp] theorem bitsWord_wordBits {n : ℕ} (x : Word n) : bitsWord n (wordBits x) = x := by
  funext i
  simp [bitsWord, wordBits]
  exact finTwoEquiv.symm_apply_apply (x i)

theorem wordBits_bitsWord {n : ℕ} (xs : List Bool) (h : xs.length = n) : wordBits (bitsWord n xs) = xs := by
  apply List.ext_getElem (by simp [h])
  intro i _ hi
  simp [wordBits, bitsWord, List.getElem?_eq_getElem hi]

/-- A reported bit string satisfies all the input rows. -/
def accepts {n : ℕ} (E : List (Equation n)) (xs : List Bool) : Bool :=
  decide (xs.length = n) && E.all fun e => dot e.1 (bitsWord n xs) == e.2

theorem accepts_iff {n : ℕ} (E : List (Equation n)) (xs : List Bool) :
    accepts E xs = true ↔ xs.length = n ∧ ∀ e ∈ E, equationHolds e (bitsWord n xs) := by
  simp [accepts, equationHolds]

private theorem dot_unit {n : ℕ} (x : Word n) (i : Fin n) :
    dot (unitWord n i.val) x = x i := by
  simp [dot, unitWord, ← Fin.ext_iff, ite_mul]

private theorem pins_iff {n k : ℕ} (x : Word n) (p : List Bool) (hlen : k+p.length = n) :
    (∀ e ∈ pins n k p, equationHolds e x) ↔ (wordBits x).drop k = p := by
  have hp (j : Fin p.length) : k+j.val < n := by have := j.isLt; omega
  have he (j : Fin p.length) : equationHolds (unitWord n (k+j.val), finTwoEquiv.symm p[j.val]) x ↔
      finTwoEquiv (x ⟨k+j.val,hp j⟩) = p[j.val] := by
    change dot (unitWord n (k+j.val)) x = _ ↔ _
    rw [dot_unit x ⟨k+j.val,hp j⟩]
    exact finTwoEquiv.eq_symm_apply
  have hs : (∀ e ∈ pins n k p, equationHolds e x) ↔
      ∀ j : Fin p.length, finTwoEquiv (x ⟨k+j.val,hp j⟩) = p[j.val] := by
    simp [pins, he]
  rw [hs]
  constructor
  · intro h
    apply List.ext_getElem (by simp; omega)
    intro j _ hj
    simpa [wordBits, List.getElem_drop] using h ⟨j,hj⟩
  · intro h j
    have hx := congrArg (fun a : List Bool => a[j.val]?) h
    have h₁ : j.val < ((wordBits x).drop k).length := by simp; omega
    simpa [List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem j.isLt, hp j, wordBits, List.getElem_drop] using hx

private theorem count_pos {n : ℕ} (E : List (Equation n)) :
    0 < affineCount E ↔ ∃ x, ∀ e ∈ E, equationHolds e x := by
  rw [affine_count_correct, Finset.card_pos]
  simp [affineSet, Finset.Nonempty]

theorem viable_correct {n : ℕ} (E : List (Equation n)) (k : ℕ) (p : List Bool) :
    viable E k p = true ↔ 0 < (completions (accepts E) k p).length := by
  simp only [viable, Bool.and_eq_true, decide_eq_true_eq, count_pos, List.length_pos_iff_exists_mem]
  constructor
  · rintro ⟨hlen, x, h⟩
    have hE : ∀ e ∈ E, equationHolds e x := fun e he => h e (List.mem_append_left _ he)
    have hpin : ∀ e ∈ pins n k p, equationHolds e x := fun e he => h e (List.mem_append_right _ he)
    refine ⟨wordBits x, (mem_completions ..).mpr ⟨by simp [hlen], (pins_iff x p hlen).mp hpin, ?_⟩⟩
    exact (accepts_iff ..).mpr ⟨length_wordBits x, by simpa using hE⟩
  · rintro ⟨xs,hxs⟩
    obtain ⟨hlen, hdrop, hacc⟩ := (mem_completions ..).mp hxs
    obtain ⟨hn, hE⟩ := (accepts_iff ..).mp hacc
    have hlen' : k+p.length = n := hlen.symm.trans hn
    refine ⟨hlen', bitsWord n xs, fun e he => ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact hE e he
    · exact (pins_iff (bitsWord n xs) p hlen').mpr (by rwa [wordBits_bitsWord xs hn]) e he

/-- Pinning a prefix preserves the full number of its accepted completions. -/
theorem completion_count {n k : ℕ} (E : List (Equation n)) (p : List Bool) (h : k+p.length=n) :
    affineCount (E++pins n k p) = (completions (accepts E) k p).length := by
  classical
  let C := completions (accepts E) k p
  let A := affineSet (E++pins n k p)
  have image : A.image wordBits = C.toFinset := by
    ext xs
    simp only [Finset.mem_image,List.mem_toFinset]
    constructor
    · rintro ⟨x,hx,rfl⟩
      have all : ∀ e ∈ E++pins n k p, equationHolds e x := by simpa [A,affineSet] using hx
      exact (mem_completions ..).mpr ⟨by simp [h],(pins_iff x p h).mp (fun e he => all e (List.mem_append_right _ he)),
        (accepts_iff ..).mpr ⟨length_wordBits _,by simpa using (fun e he => all e (List.mem_append_left _ he) :
          ∀ e ∈ E, equationHolds e x)⟩⟩
    · intro hx
      obtain ⟨len,drop,acc⟩ := (mem_completions ..).mp hx
      have hn : xs.length = n := len.trans h
      have bits := wordBits_bitsWord xs hn
      refine ⟨bitsWord n xs,?_,bits⟩
      change _ ∈ affineSet _
      simp only [affineSet,Finset.mem_filter,Finset.mem_univ,true_and]
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact ((accepts_iff ..).mp acc).2 e he
      · exact (pins_iff (bitsWord n xs) p h).mpr ((congrArg (List.drop k) bits).trans drop) e he
  have inj : Function.Injective (@wordBits n) := fun x y eq => by simpa using congrArg (bitsWord n) eq
  rw [affine_count_correct,← List.toFinset_card_of_nodup (completions_nodup ..)]
  change A.card = C.toFinset.card
  rw [← image,Finset.card_image_of_injective _ inj]

/-- The executable DFS issues at most 1+2*n*r queries when it returns r words, for every cap. -/
theorem enumerate_spec {n : ℕ} (E : List (Equation n)) (cap : ℕ) :
    let out := search (viable E) n [] cap
    out.words = (completions (accepts E) n []).take cap ∧
      out.probes ≤ 1 + 2*n*out.words.length :=
  ⟨search_words _ _ (viable_correct E) .., search_probes _ _ (viable_correct E) ..⟩

end AffinePrefixEnumeration

end AffinePrefixEnumeration

section AffineQueryEncoding

namespace AffinePrefixEnumeration

open EditGV897.Main

/-- A pinned coordinate can be emitted with a single column equality test. -/
def pinPayload (n index : ℕ) (val : Bool) :=
  (List.ofFn fun col : Fin n => decide (col.val = index)) ++ [val]

private theorem code_pin (n k : ℕ) (b : Bool) :
    rowPayload (unitWord n k,finTwoEquiv.symm b) = pinPayload n k b := by
  have hc (i : Fin n) : decide (unitWord n k i ≠ 0) = decide (i.val = k) := by
    by_cases he : i.val = k <;> simp [unitWord,he]
  have hb : decide (finTwoEquiv.symm b ≠ 0) = b := by cases b <;> decide
  simp only [rowPayload,pinPayload,hc]
  exact congrArg (fun v => (List.ofFn fun i : Fin n => decide (i.val = k)) ++ [v]) hb

end AffinePrefixEnumeration

end AffineQueryEncoding

section CountedUnranking

namespace BoundedEnumeration

theorem unrank_eq_get (accept : List Bool → Bool) (count : ℕ → List Bool → ℕ) (n : ℕ)
    (counts : ∀ k p, k+p.length=n → count k p = (completions accept k p).length)
    (k : ℕ) (p : List Bool) (hp : k+p.length=n) (i : ℕ) (hi : i < (completions accept k p).length) :
    unrank count k p i = (completions accept k p)[i] := by
  induction k generalizing p i with
  | zero =>
    cases h : accept p
    · simp [completions,h] at hi
    · have eq : i=0 := by simp [completions,h] at hi; omega
      subst i
      simp [unrank,completions,h]
  | succ k ih =>
    have length (b : Bool) : k+(b::p).length=n := by simp; omega
    have left := counts k (false::p) (length false)
    simp only [unrank,left,completions]
    by_cases inLeft : i < (completions accept k (false::p)).length
    · rw [if_pos inLeft,List.getElem_append_left inLeft]
      exact ih _ (length false) i inLeft
    · rw [if_neg inLeft,List.getElem_append_right (by omega)]
      apply ih _ (length true)

/-- Increasing ranks enumerate every solution once in precisely the reference order. -/
theorem unrank_all (accept : List Bool → Bool) (count : ℕ → List Bool → ℕ) (n : ℕ)
    (counts : ∀ k p, k+p.length=n → count k p = (completions accept k p).length)
    (k : ℕ) (p : List Bool) (hp : k+p.length=n) :
    (List.range (count k p)).map (unrank count k p) = completions accept k p := by
  rw [counts k p hp]
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simpa using unrank_eq_get accept count n counts k p hp i h₂

end BoundedEnumeration

end CountedUnranking

section AffineRankEnumeration

namespace AffinePrefixEnumeration

open BoundedEnumeration EditGV897.Main

/-- One count supplies the number of outputs. At most n further counts reconstruct
any requested output from its rank, including the unique empty word when n=0. -/
theorem rankedSolutions_eq {n : ℕ} (E : List (Equation n)) :
    (List.range (affineCount E)).map (rankedSolution E) = completions (accepts E) n [] := by
  have h := unrank_all (accepts E) (fun k p => affineCount (E++pins n k p)) n (fun k p h => completion_count E p h)
    n [] (by simp)
  change (List.range (affineCount E)).map (unrank (fun k p => affineCount (E++pins n k p)) n []) = _
  simpa only [show pins n n []=[] by simp [pins],List.append_nil] using h

end AffinePrefixEnumeration

end AffineRankEnumeration

section HamiltonianParityPolynomial

namespace DirectedHamiltonicity.Main.Multidigraph

open Polynomial

open scoped BigOperators

open Classical

variable {V E : Type} [Fintype V] [instV : DecidableEq V] [Fintype E] [DecidableEq E]

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V)

omit [DecidableEq V] [DecidableEq E] in
/-- Counting path labels with multiplicity gives the coefficient over the parity field. -/
theorem coeff_hamPathPoly_monomials (b : ℕ) :
    (H.hamPathPoly (fun e => (X : (ZMod 2)[X]) ^ w e) s t).coeff b =
      (H.weightedPathCount w s t (b : ℤ) : ZMod 2) := by
  classical
  simp only [hamPathPoly, Finset.prod_pow_eq_pow_sum, finsetSum_coeff, coeff_X_pow,
    weightedPathCount, pathWeight, Int.natCast_inj, Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro P _
  simp [eq_comm]

omit [DecidableEq V] [DecidableEq E] in
/-- Every path has exactly `card V - 1` arcs, including paths using parallel copies. -/
theorem weightedPathCount_eq_zero_outside {W : ℕ} (hw : ∀ e, w e ≤ W) (B : ℤ)
    (hout : B < 0 ∨ ((Fintype.card V - 1) * W : ℕ) < B) :
    H.weightedPathCount w s t B = 0 := by
  classical
  unfold weightedPathCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro P hP
  obtain ⟨_, hB⟩ := Finset.mem_filter.mp hP
  have hweight : pathWeight w P ≤ (Fintype.card V - 1) * W := by
    calc
      _ ≤ ∑ _i : Fin (Fintype.card V - 1), W := Finset.sum_le_sum fun i _ => hw (P i)
      _ = _ := by simp
  omega

private theorem augmented_det_identity (hst : s ≠ t) (hn : H.IsNormalized w s t)
    (R : (i : Internal s t) → Finset (H.incomingWeights w i.1)) :
    H.hamPathPoly (fun e => (X : (ZMod 2)[X]) ^ w e) s t =
      ∑ x, (H.augLaplacian w s t x R).det := by
  classical
  exact DirectedHamiltonicity.Main.lemma8 H s t hst hn.1 hn.2.1 hn.2.2.1
    (fun e => (X : (ZMod 2)[X]) ^ w e) (H.augGraph w s t R) (fun _ => rfl)
    (fun a => a.1.2.2) (fun a => (X : (ZMod 2)[X]) ^ (a.2.1.1 : ℕ))

omit [DecidableEq E] in
private theorem det_zero_of_missing (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (x : Finset (Internal s t)) (hx : x ∉ H.survivors w s t R) :
    (H.augLaplacian w s t x R).det = 0 := by
  have he : instV = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  subst instV
  classical
  simp only [survivors, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  push Not at hx
  obtain ⟨i, _, hi⟩ := hx
  let u : {v // v ≠ s} := ⟨i.1, i.2.1⟩
  exact Matrix.det_eq_zero_of_row_eq_zero (A := H.augLaplacian w s t x R) u
    (fun j => congrFun hi j)

/-- If every surviving set was enumerated, additional distinct sets contribute zero.
This justifies ignoring multiplicities even when the same set occurs in several trials. -/
theorem hamPathPoly_eq_covered_det_sum (hst : s ≠ t) (hn : H.IsNormalized w s t)
    (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (S : Finset (Finset (Internal s t))) (hcover : H.survivors w s t R ⊆ S) :
    H.hamPathPoly (fun e => (X : (ZMod 2)[X]) ^ w e) s t =
      ∑ x ∈ S, (H.augLaplacian w s t x R).det := by
  rw [augmented_det_identity H w s t hst hn R]
  symm
  exact Finset.sum_subset (Finset.subset_univ S) (fun x _ hx =>
    det_zero_of_missing H w s t R x (fun h => hx (hcover h)))

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianParityPolynomial

section HamiltonianParityEstimator

namespace DirectedHamiltonicity.Main.Multidigraph

open FiniteSampling Classical Polynomial

open scoped BigOperators

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V)

/-- The value returned by the cutoff and the sum over distinct reported sets.
The size of the determinant and enumeration computations is a separate machine obligation. -/
noncomputable def parityEstimate
    (code : H.NonzeroCoeffs w s t ↪ CoinBlock (H.NonzeroCoeffs w s t)) (m : ℕ) (B : ℤ)
    (z : H.RandomMasks w s t × (Fin m → CoinBlock (H.NonzeroCoeffs w s t))) : ZMod 2 :=
  if B < 0 ∨ 12 * m < reports (H.coinFamily w s t code) z.1 z.2 then 0
  else (∑ x ∈ covered (H.coinFamily w s t code) z.1 z.2,
    (H.augLaplacian w s t x z.1).det).coeff B.toNat

/-- The high-level parity estimator is correct on at least five sixths of every sufficiently
long uniform tape, for every integer target. The conclusion concerns the estimator itself. -/
theorem parityEstimate_on_coin_tape (hst : s ≠ t) (hn : H.IsNormalized w s t)
    (index : H.MaskIndex w s t ≃ Fin (Fintype.card (H.MaskIndex w s t)))
    (code : H.NonzeroCoeffs w s t ↪ CoinBlock (H.NonzeroCoeffs w s t)) (B : ℤ) :
    let m := samplingBlockSize (Fintype.card V) (H.samplingDegree w) * (Fintype.card V + 4)
    ∀ (L : ℕ) (hL : H.parityCoinCount w s t m ≤ L),
      5 / 6 ≤ probability (fun c : Fin L → Bool =>
        H.parityEstimate w s t code m B (H.parityCoinBlocks w s t index m (fun i => c (Fin.castLE hL i))) =
          (H.weightedPathCount w s t B : ZMod 2)) := by
  intro m L hL
  let p := fun z => H.parityEstimate w s t code m B z = (H.weightedPathCount w s t B : ZMod 2)
  let e := H.parityCoinBlocks w s t index m
  change 5 / 6 ≤ probability (fun c : Fin L → Bool => (fun z => p (e z)) (fun i => c (Fin.castLE hL i)))
  rw [probability_prefix hL (fun z => p (e z)), probability_equiv e p]
  apply (H.parity_coverage_probability w s t hst hn code).trans
  apply probability_mono
  rintro z ⟨hcover, hcount⟩
  dsimp only [p]
  by_cases hB : B < 0
  · have hc : H.weightedPathCount w s t B = 0 := H.weightedPathCount_eq_zero_outside w s t
      (W := ∑ e, w e) (fun e => Finset.single_le_sum (fun j _ => Nat.zero_le (w j)) (Finset.mem_univ e))
      B (Or.inl hB)
    simp [parityEstimate, hB, hc]
  · have hz : (B.toNat : ℤ) = B := Int.toNat_of_nonneg (le_of_not_gt hB)
    have hsum := H.hamPathPoly_eq_covered_det_sum w s t hst hn z.1 _ hcover
    have hcut : ¬ (B < 0 ∨ 12 * m < reports (H.coinFamily w s t code) z.1 z.2) :=
      not_or.mpr ⟨hB, not_lt_of_ge hcount⟩
    rw [parityEstimate, if_neg hcut, ← hsum]
    simpa only [hz] using H.coeff_hamPathPoly_monomials w s t B.toNat

omit [DecidableEq E] in
/-- The full tape budget counts the shared diagonal mask once and one block per trial. -/
theorem parityCoinCount_le (m : ℕ) :
    H.parityCoinCount w s t m ≤
      Fintype.card V * Fintype.card E + m * (Fintype.card V * (Fintype.card E + 1)) := by
  classical
  unfold parityCoinCount
  apply Nat.add_le_add _ (Nat.mul_le_mul_left m (H.coefficient_block_width w s t))
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _i : Internal s t, Fintype.card E := by
      apply Finset.sum_le_sum
      intro i _
      rw [Fintype.card_coe]
      exact Finset.card_image_le.trans (Finset.card_le_univ _)
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact Nat.mul_le_mul_right _ (Fintype.card_subtype_le _)

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianParityEstimator

section HamiltonianCoinEncoding

namespace DirectedHamiltonicity.Main.Multidigraph

open FiniteSampling

open scoped BigOperators

variable {n : ℕ} {E : Type} [Fintype E]

variable (H : Multidigraph (Fin n) E) (w : E → ℕ) (s t : Fin n)

theorem coeffRadixProduct_eq_card : H.coeffRadixProduct w s t = Fintype.card (H.NonzeroCoeffs w s t) := by
  simpa using (Fintype.card_congr (H.coefficientRank w s t)).symm

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianCoinEncoding

section HamiltonianSamplingRows

namespace DirectedHamiltonicity.Main.Multidigraph

open Classical Polynomial

open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E]

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V)

private abbrev Bit := ZMod 2

/-- The constant coordinate of a lifted indicator is one. -/
noncomputable def liftedIndicator (X : Finset (Internal s t)) : Option (Internal s t) → ZMod 2
  | none => 1
  | some i => if i ∈ X then 1 else 0

omit [Fintype V] [Fintype E] in
private theorem tail_value (x : Finset (Internal s t)) (e : E) :
    liftedIndicator s t x (tailCoordinate s t (H.tail e)) =
      if H.KeepArc s t x e then 1 else 0 := by
  classical
  by_cases h : H.tail e ≠ s ∧ H.tail e ≠ t <;> simp [tailCoordinate, liftedIndicator, KeepArc, h]

private theorem subtype_terms {A : Type} [Fintype A] (p : A → Prop) [Fintype {a // p a}]
    (g : A → Bit) : (∑ a : {a // p a}, g a.1) = ∑ a : A, if p a then g a else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) g).symm

theorem diagonalForm_eval (x : Finset (Internal s t)) (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (i : Internal s t) (b : H.incomingWeights w i.1) :
    H.diagonalForm w s t R i b ⬝ᵥ liftedIndicator s t x = H.diagCoeffs w s t x R i b := by
  classical
  simp only [diagonalForm, add_dotProduct, sum_dotProduct, diagCoeffs, augLaplacian,
    reducedLaplacian, Matrix.submatrix_apply, laplacian, if_true, Finset.sum_filter,
    Fintype.sum_sum_type, subXR, addArcs, subXRLabel, Sum.elim_inl, Sum.elim_inr, augGraph,
    Polynomial.coeff_add, Polynomial.finsetSum_coeff]
  apply congrArg₂ (· + ·)
  · let g := fun e : E => (if H.head e = i.1 then (X : Polynomial Bit) ^ w e else 0).coeff b.1
    change _ = ∑ e : {e // H.KeepArc s t x e}, g e.1
    rw [subtype_terms]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hv : H.head e = i.1 <;> by_cases hb : w e = b.1 <;>
      by_cases hk : H.KeepArc s t x e <;>
      simp [g, hv, hb, Ne.symm, Polynomial.coeff_X_pow, single_dotProduct,
        tail_value, hk, eq_comm]
  · apply Finset.sum_congr rfl
    intro e _
    by_cases hv : e.1.1 = i.1 <;> by_cases hb : e.2.1.1 = b.1 <;>
      simp [hv, hb, Polynomial.coeff_X_pow, single_dotProduct, liftedIndicator]
    exact Ne.symm hb

theorem mem_sampled_iff_linear (x : Finset (Internal s t)) (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (a : (i : Internal s t) → H.CoeffVec w i.1) :
    x ∈ H.sampled w s t a R ↔ ∀ i, H.samplingRow w s t R a i ⬝ᵥ liftedIndicator s t x = 1 := by
  classical
  simp only [sampled, Finset.mem_filter, Finset.mem_univ, true_and, samplingRow, add_dotProduct,
    sum_dotProduct, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul, diagonalForm_eval]
  rfl

/-- The same system in the conventional form with one column per internal vertex and an
explicit right-hand side. The matrix and right-hand side are independent of the tested set. -/
theorem mem_sampled_iff_matrix_rows (x : Finset (Internal s t)) (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (a : (i : Internal s t) → H.CoeffVec w i.1) :
    x ∈ H.sampled w s t a R ↔ ∀ i,
      (∑ j : Internal s t, H.samplingRow w s t R a i (some j) * (if j ∈ x then 1 else 0)) =
        1 - H.samplingRow w s t R a i none := by
  rw [mem_sampled_iff_linear]
  apply forall_congr'
  intro i
  simp only [dotProduct, Fintype.sum_option, liftedIndicator, mul_one]
  rw [eq_sub_iff_add_eq, add_comm]

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianSamplingRows

section HamiltonianAffineEnumeration

namespace DirectedHamiltonicity.Main.Multidigraph

open EditGV897.Main AffinePrefixEnumeration BoundedEnumeration

open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E] {q : ℕ}

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V)

theorem sampled_iff_affine (order : Fin q ≃ Internal s t)
    (r : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (a : (i : Internal s t) → H.CoeffVec w i.1) (x : Finset (Internal s t)) :
    x ∈ H.sampled w s t a r ↔ ∀ row ∈ H.samplingSystem w s t order r a,
      equationHolds row (numberedIndicator s t order x) := by
  classical
  rw [H.mem_sampled_iff_matrix_rows]
  have he (i : Internal s t) :
      dot (fun j => H.samplingRow w s t r a i (some (order j))) (numberedIndicator s t order x) =
        ∑ j, H.samplingRow w s t r a i (some j) * (if j ∈ x then 1 else 0) := by
    exact order.sum_comp (fun j => H.samplingRow w s t r a i (some j) * (if j ∈ x then 1 else 0))
  simp only [samplingSystem, List.forall_mem_ofFn_iff, equationHolds, he]
  exact order.surjective.forall

/-- Exhausting one trial gives exactly its sampled subsets, in a bijective bit-string
representation. This statement also applies when there are no internal vertices. -/
theorem affine_trial_words (order : Fin q ≃ Internal s t)
    (r : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (a : (i : Internal s t) → H.CoeffVec w i.1) :
    (completions (accepts (H.samplingSystem w s t order r a)) q []).toFinset =
      (H.sampled w s t a r).image (fun x => wordBits (numberedIndicator s t order x)) := by
  classical
  ext xs
  simp only [List.mem_toFinset, mem_completions, List.length_nil, Nat.add_zero, Finset.mem_image]
  let e := numberedIndicator s t order
  constructor
  · rintro ⟨hlen, _, hacc⟩
    let x := e.symm (bitsWord q xs)
    refine ⟨x,(H.sampled_iff_affine w s t order r a x).mpr ?_,?_⟩
    · simpa [x,e] using ((accepts_iff _ _).mp hacc).2
    · simpa [x,e] using wordBits_bitsWord xs hlen
  · rintro ⟨x,hx,rfl⟩
    refine ⟨length_wordBits _, by simp [wordBits], (accepts_iff ..).mpr ⟨length_wordBits _, ?_⟩⟩
    simpa using (H.sampled_iff_affine w s t order r a x).mp hx

theorem affine_trial_length (order : Fin q ≃ Internal s t)
    (r : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (a : (i : Internal s t) → H.CoeffVec w i.1) :
    (completions (accepts (H.samplingSystem w s t order r a)) q []).length =
      (H.sampled w s t a r).card := by
  rw [← List.toFinset_card_of_nodup (completions_nodup ..), H.affine_trial_words]
  apply Finset.card_image_of_injective
  intro x y h
  apply (numberedIndicator s t order).injective
  simpa using congrArg (bitsWord q) h

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianAffineEnumeration

section TabulatedDeterminant

/-! A tabulated Bird determinant, with counts of ring operations and bounds on polynomial degrees. -/

section

namespace BirdDet.Tabulated

open scoped BigOperators

@[simp] theorem matrix_table {R : Type*} {n : ℕ} (f : Fin n → Fin n → R) (i j : Fin n) :
    matrix (table f) i j = f i j := by simp [matrix, table]

variable {R : Type*} {n : ℕ}

theorem sumList_value [CommRing R] {ι : Type*} (f : ι → Counted R) (xs : List ι) :
    (sumList f xs).value = (xs.map fun i => (f i).value).sum := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [sumList, ih]

theorem sumList_ops [Zero R] [Add R] {ι : Type*} (f : ι → Counted R) (xs : List ι) (b : ℕ)
    (h : ∀ i, (f i).ops ≤ b) : (sumList f xs).ops ≤ xs.length * (b+1) := by
  induction xs with
  | nil => simp [sumList]
  | cons i xs ih =>
    simp only [sumList, List.length_cons, Nat.succ_mul]
    have := h i
    omega

private theorem entry_value [CommRing R] (A F : Table R n) (i j : Fin n) :
    (entry A F i j).value = BirdDet.Spec.stepEntry (matrix A) (matrix F) i j := by
  simp only [entry, diagonalTerm, productTerm, sumList_value, ← List.ofFn_eq_map, List.sum_ofFn,
    BirdDet.Spec.stepEntry_eq, Matrix.of_apply]
  simp only [apply_ite Counted.value]
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

private theorem entry_ops [Zero R] [Add R] [Mul R] [Neg R] (A F : Table R n) (i j : Fin n) :
    (entry A F i j).ops ≤ 3 * (n+1) := by
  let f := fun k : Fin n => (⟨if i < k then matrix F k k else 0, 0⟩ : Counted R)
  let g := fun k : Fin n => if i < k then (⟨matrix F i k * matrix A k j, 1⟩ : Counted R) else ⟨0,0⟩
  have hf := sumList_ops f (List.finRange n) 0 (fun _ => Nat.le_refl 0)
  have hg := sumList_ops g (List.finRange n) 1 (fun k => by by_cases h : i < k <;> simp [g, h])
  simp only [List.length_finRange] at hf hg
  change (sumList f _).ops + (sumList g _).ops + 3 ≤ _
  omega

theorem layers_value [CommRing R] (A : Table R n) (k : ℕ) :
    matrix (layers A k).value = (BirdDet.Spec.stepEntry (matrix A))^[k] (matrix A) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    ext i j
    simp only [layers, matrix_table, entry_value, ih, Function.iterate_succ_apply']

theorem layers_ops [Zero R] [Add R] [Mul R] [Neg R] (A : Table R n) (k : ℕ) :
    (layers A k).ops ≤ k * (n*n * (3*(n+1))) := by
  induction k with
  | zero => simp [layers]
  | succ k ih =>
    simp only [layers, matrix_table]
    rw [Nat.succ_mul k]
    apply Nat.add_le_add ih
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, 3*(n+1) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => entry_ops A (layers A k).value i j
      _ = _ := by simp [Nat.mul_assoc]

private theorem sum_tail_fin [CommRing R] (i : Fin n) (f : ℕ → R) :
    BirdDet.sumFrom n (i.val+1) f=∑ j ∈ Finset.Ioi i, f j.val := by
  have suffix (lo : ℕ) : BirdDet.sumFrom n lo f=∑ j ∈ Finset.Ico lo n, f j := by
    induction lo using BirdDet.sumFrom_induct n with
    | step lo h ih => rw [BirdDet.sumFrom_step n lo f h,ih,← Finset.sum_eq_sum_Ico_succ_bot h f]
    | stop lo h => rw [BirdDet.sumFrom_stop n lo f h,Finset.Ico_eq_empty h,Finset.sum_empty]
  rw [suffix]
  have indexes : Finset.Ico (i.val+1) n=(Finset.range n).filter (i.val < ·) := by
    ext j
    simp only [Finset.mem_Ico,Finset.mem_filter,Finset.mem_range]
    omega
  rw [indexes,Finset.sum_filter,← Fin.sum_univ_eq_sum_range]
  simp [← Finset.sum_filter,Finset.filter_lt_eq_Ioi]

private theorem array_iterations [CommRing R] (data : Array R) (sz : data.size=n*n)
    (h : ℕ) (i j : Fin n) :
    ((BirdDet.stepEntry n data)^[h] (BirdDet.get n data)) i.val j.val =
      (BirdDet.Spec.stepEntry (.ofArray data sz))^[h] (.ofArray data sz) i j := by
  rw [Matrix.ofArray_eq_of_getD]
  induction h generalizing i j with
  | zero => simp [BirdDet.get_eq]
  | succ h ih =>
    simp_rw [Function.iterate_succ_apply',BirdDet.stepEntry_eq,BirdDet.Spec.stepEntry_eq,sum_tail_fin,ih,
      Matrix.of_apply,BirdDet.get_eq]

private theorem array_spec [CommRing R] (data : Array R) (sz : data.size=n*n) :
    BirdDet.birdDet n data=BirdDet.Spec.birdDet (.ofArray data sz) := by
  cases n with
  | zero => rw [BirdDet.birdDet_zero,BirdDet.Spec.birdDetSpec_zero]
  | succ n => simp [BirdDet.birdDet_succ,BirdDet.Spec.birdDetSpec_succ,← array_iterations data sz n]

/-- Relate the matrix recurrence to mathlib's public row-major determinant theorem. -/
private theorem matrix_spec [CommRing R] (A : Matrix (Fin n) (Fin n) R) :
    A.det=BirdDet.Spec.birdDet A := by
  let data := Array.ofFn fun k : Fin (n*n) => A k.divNat k.modNat
  have sz : data.size=n*n := Array.size_ofFn
  have rep : Matrix.ofArray data sz=A := Matrix.ofArray_ofFn A
  exact (congrArg Matrix.det rep.symm).trans ((BirdDet.det_eq_birdDet data sz).trans
    ((array_spec data sz).trans (congrArg BirdDet.Spec.birdDet rep)))

theorem determinant_value [CommRing R] (A : Table R n) : (determinant A).value = (matrix A).det := by
  rw [matrix_spec]
  cases n with
  | zero => simp [determinant]
  | succ k =>
    rw [BirdDet.Spec.birdDetSpec_succ, neg_one_pow_eq_ite]
    by_cases h : Even k <;> simp [determinant, h, layers_value]

theorem determinant_ops [Zero R] [One R] [Add R] [Mul R] [Neg R] (A : Table R n) :
    (determinant A).ops ≤ (n-1) * (n*n * (3*(n+1))) + 1 := by
  cases n with
  | zero => simp [determinant]
  | succ k =>
    have h := layers_ops A k
    by_cases he : Even k <;> simp [determinant, he] <;> omega

open Polynomial

/-- Input degree at most W implies degree at most (k+1)W in every entry of the kth table. -/
theorem layers_degree {K : Type*} [CommRing K] (A : Table (Polynomial K) n) {W : ℕ}
    (hA : ∀ i j, (matrix A i j).natDegree ≤ W) (k : ℕ) (i j : Fin n) :
    (matrix (layers A k).value i j).natDegree ≤ (k+1)*W := by
  induction k generalizing i j with
  | zero => simpa [layers] using hA i j
  | succ k ih =>
    let F := matrix (layers A k).value
    have hsum (a : Fin n) :
        (∑ l ∈ Finset.Ioi a, F l l).natDegree ≤ (k+1)*W :=
      natDegree_sum_le_of_forall_le _ _ (fun l _ => ih l l)
    have hm (a b c : Fin n) : (F a b * matrix A b c).natDegree ≤ (k+1)*W + W :=
      natDegree_mul_le.trans (Nat.add_le_add (ih a b) (hA b c))
    simp only [layers, matrix_table, entry_value, BirdDet.Spec.stepEntry_eq, Matrix.of_apply]
    rw [Nat.succ_mul (k+1) W]
    apply natDegree_add_le_of_degree_le
    · exact natDegree_mul_le.trans (Nat.add_le_add (by simpa [F] using hsum i) (hA i j))
    · exact natDegree_sum_le_of_forall_le _ _ (fun l _ => hm i l j)

theorem determinant_degree {K : Type*} [CommRing K] (A : Table (Polynomial K) n) {W : ℕ}
    (hA : ∀ i j, (matrix A i j).natDegree ≤ W) : (matrix A).det.natDegree ≤ n*W := by
  rw [← determinant_value]
  cases n with
  | zero => simp [determinant]
  | succ k =>
    have h := layers_degree A hA k 0 0
    by_cases he : Even k <;> simpa [determinant, he] using h

end BirdDet.Tabulated

end

end TabulatedDeterminant

section TruncatedPolynomialDeterminant

/-! Compute the low coefficients of a determinant using fixed-length arrays of coefficients. -/

namespace BirdDet.Tabulated

open scoped BigOperators

section Map

variable {R S : Type*} [Zero R] [One R] [Add R] [Mul R] [Neg R]

variable [Zero S] [One S] [Add S] [Mul S] [Neg S]

/-- These five identities suffice for using a different concrete representation at every gate. -/
structure PreservesArithmetic (f : R → S) : Prop where
  zero : f 0 = 0
  one : f 1 = 1
  add : ∀ x y, f (x+y) = f x + f y
  mul : ∀ x y, f (x*y) = f x * f y
  neg : ∀ x, f (-x) = -f x

variable {f : R → S} (h : PreservesArithmetic f)

include h

private theorem map_sumList {ι : Type*} (g : ι → Counted R) (g' : ι → Counted S)
    (hg : ∀ i, f (g i).value = (g' i).value) (xs : List ι) :
    f (sumList g xs).value = (sumList g' xs).value := by
  induction xs with
  | nil => exact h.zero
  | cons i xs ih => simp only [sumList, h.add, hg, ih]

private theorem map_entry {n : ℕ} (A F : Table R n) (B G : Table S n)
    (hA : ∀ i j, f (matrix A i j) = matrix B i j)
    (hF : ∀ i j, f (matrix F i j) = matrix G i j) (i j : Fin n) :
    f (entry A F i j).value = (entry B G i j).value := by
  have hd := map_sumList h (diagonalTerm F i) (diagonalTerm G i) (fun k => by
    by_cases hk : i < k <;> simp [diagonalTerm, hk, hF, h.zero]) (List.finRange n)
  have hr := map_sumList h (productTerm A F i j) (productTerm B G i j) (fun k => by
    by_cases hk : i < k <;> simp [productTerm, hk, h.mul, hA, hF, h.zero]) (List.finRange n)
  simp only [entry, h.add, h.mul, h.neg, hd, hr, hA]

private theorem map_layers {n : ℕ} (A : Table R n) (B : Table S n)
    (hA : ∀ i j, f (matrix A i j) = matrix B i j) (k : ℕ) (i j : Fin n) :
    f (matrix (layers A k).value i j) = matrix (layers B k).value i j := by
  induction k generalizing i j with
  | zero => exact hA i j
  | succ k ih =>
    simp only [layers, matrix_table]
    exact map_entry h A _ B _ hA ih i j

theorem map_determinant {n : ℕ} (A : Table R n) (B : Table S n)
    (hA : ∀ i j, f (matrix A i j) = matrix B i j) :
    f (determinant A).value = (determinant B).value := by
  cases n with
  | zero => exact h.one
  | succ k =>
    have hv := map_layers h A B hA k 0 0
    by_cases he : Even k <;> simp [determinant, he, h.neg, hv]

end Map

namespace CoeffArray

variable {K : Type*} {width : ℕ}

@[simp] theorem get_ofFn (f : Fin width → K) (i : Fin width) : (ofFn f).get i = f i := by
  simp [get, ofFn]

@[ext] theorem ext {u v : CoeffArray K width} (h : ∀ i, u.get i = v.get i) : u = v := by
  cases u with
  | mk a =>
    cases v with
    | mk b =>
      congr
      apply Vector.ext
      intro i hi
      exact h ⟨i,hi⟩

variable [CommRing K]

@[simp] theorem get_fromPolynomial (p : Polynomial K) (i : Fin width) :
    (fromPolynomial width p).get i = p.coeff i.val := get_ofFn _ _

theorem preserves (width : ℕ) : PreservesArithmetic (fromPolynomial (K := K) width) where
  zero := by
    ext i
    change (fromPolynomial width (0 : Polynomial K)).get i = (ofFn _).get i
    simp
  one := by ext i; change (fromPolynomial width (1 : Polynomial K)).get i = (ofFn _).get i
            simp [Polynomial.coeff_one]
  add p q := by ext i; change (fromPolynomial width (p+q)).get i = (ofFn _).get i; simp
  neg p := by ext i; change (fromPolynomial width (-p)).get i = (ofFn _).get i; simp
  mul p q := by
    ext i
    change (fromPolynomial width (p*q)).get i = (ofFn _).get i
    simp only [get_ofFn, get_fromPolynomial, convolve, sumList_value, ← List.ofFn_eq_map,
      List.sum_ofFn, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact (Fin.sum_univ_eq_sum_range _ _).symm

/-- A coefficient-array execution computes every requested low coefficient of the determinant. -/
theorem determinant_coeff {n : ℕ} (A : Table (Polynomial K) n) (B : Table (CoeffArray K width) n)
    (h : ∀ i j, fromPolynomial width (matrix A i j) = matrix B i j) (b : Fin width) :
    (determinant B).value.get b = (matrix A).det.coeff b.val := by
  have he := map_determinant (preserves width) A B h
  rw [← he, determinant_value, get_fromPolynomial]

end CoeffArray

end BirdDet.Tabulated

end TruncatedPolynomialDeterminant

section HamiltonianParityInput

namespace DirectedHamiltonicity.Main

theorem readTarget_encInt (cap : ℕ) (z : ℤ) (suffix : List Bool) :
    readTarget cap (encInt z ++ suffix) =
      if 0 ≤ z ∧ z ≤ (cap : ℤ) then some z.toNat else none := by
  cases z with
  | ofNat n =>
    have hsign : ¬((n : ℤ) < 0) := not_lt.mpr (Int.natCast_nonneg n)
    simpa [Int.ofNat_eq_natCast, readTarget, encInt, encNat, hsign, List.append_assoc] using
      BoundedBinaryInput.readAtMost_encoded cap n suffix
  | negSucc n => simp [readTarget, encInt]

end DirectedHamiltonicity.Main

end HamiltonianParityInput

section HamiltonianParityDeterminant

namespace DirectedHamiltonicity.Main.Multidigraph

open FiniteSampling Polynomial BirdDet.Tabulated

open scoped BigOperators

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V)

/-- The added arcs only use weights already present among the incoming arcs. -/
theorem augLaplacian_entry_degree {W : ℕ} (hw : ∀ e, w e ≤ W)
    (x : Finset (Internal s t)) (r : H.RandomMasks w s t) (i j : {v // v ≠ s}) :
    ((H.augLaplacian w s t x r) i j).natDegree ≤ W := by
  classical
  have hlabel (e) : (H.subXRLabel w s t x r e).natDegree ≤ W := by
    cases e with
    | inl e => exact (natDegree_X_pow_le _).trans (hw e.1)
    | inr a =>
      have hb := a.2.1.2
      obtain ⟨e, _, he⟩ := Finset.mem_image.mp hb
      exact (natDegree_X_pow_le _).trans (he ▸ hw e)
  change (((H.subXR w s t x r).laplacian (H.subXRLabel w s t x r)) i.val j.val).natDegree ≤ W
  unfold laplacian
  split
  · exact natDegree_sum_le_of_forall_le _ _ (fun e _ => hlabel e)
  · rw [natDegree_neg]
    exact natDegree_sum_le_of_forall_le _ _ (fun e _ => hlabel e)

/-- Number the rows of the reduced Laplacian in any fixed order to obtain the initial table. -/
noncomputable def laplacianTable {q : ℕ} (e : Fin q ≃ {v // v ≠ s})
    (x : Finset (Internal s t)) (r : H.RandomMasks w s t) : Table (Polynomial (ZMod 2)) q :=
  table fun i j => H.augLaplacian w s t x r (e i) (e j)

theorem tabulated_laplacian_det {q : ℕ} (e : Fin q ≃ {v // v ≠ s})
    (x : Finset (Internal s t)) (r : H.RandomMasks w s t) :
    let v := determinant (H.laplacianTable w s t e x r)
    v.value = (H.augLaplacian w s t x r).det ∧ v.ops ≤ (q-1)*(q*q*(3*(q+1)))+1 := by
  refine ⟨?_, determinant_ops _⟩
  rw [determinant_value]
  have he : matrix (H.laplacianTable w s t e x r) = (H.augLaplacian w s t x r).submatrix e e := by
    ext i j
    simp [laplacianTable]
  rw [he, Matrix.det_submatrix_equiv_self]

theorem augLaplacian_det_degree {W : ℕ} (hw : ∀ e, w e ≤ W)
    (x : Finset (Internal s t)) (r : H.RandomMasks w s t) :
    (H.augLaplacian w s t x r).det.natDegree ≤ (Fintype.card V-1)*W := by
  let e := (Fintype.equivFin {v : V // v ≠ s}).symm
  let A := H.laplacianTable w s t e x r
  have hA (i j) : (matrix A i j).natDegree ≤ W := by
    simpa [A, laplacianTable] using H.augLaplacian_entry_degree w s t hw x r (e i) (e j)
  rw [← (H.tabulated_laplacian_det w s t e x r).1, determinant_value]
  simpa [Fintype.card_subtype_compl] using determinant_degree A hA

/-- An oversized target gives zero even on tapes on which the sampler misses a survivor. -/
theorem parityEstimate_zero_outside {W : ℕ} (hw : ∀ e, w e ≤ W)
    (code : H.NonzeroCoeffs w s t ↪ CoinBlock (H.NonzeroCoeffs w s t)) (m : ℕ) (B : ℤ)
    (z : H.RandomMasks w s t × (Fin m → CoinBlock (H.NonzeroCoeffs w s t)))
    (hout : B < 0 ∨ ((Fintype.card V - 1)*W : ℕ) < B) :
    H.parityEstimate w s t code m B z = 0 := by
  unfold parityEstimate
  split
  · rfl
  · rename_i h
    have hn : ¬B < 0 := fun hb => h (Or.inl hb)
    have hg := hout.resolve_left hn
    have hB : (Fintype.card V-1)*W < B.toNat := by omega
    apply coeff_eq_zero_of_natDegree_lt
    exact (natDegree_sum_le_of_forall_le _ _
      (fun x _ => H.augLaplacian_det_degree w s t hw x z.1)).trans_lt hB

theorem laplacian_coefficient {q width : ℕ} (e : Fin q ≃ {v // v ≠ s})
    (x : Finset (Internal s t)) (r : H.RandomMasks w s t) (b : Fin width) :
    (determinant (H.laplacianCoefficients w s t e x r width)).value.get b =
      (H.augLaplacian w s t x r).det.coeff b.val := by
  have h := CoeffArray.determinant_coeff (H.laplacianTable w s t e x r)
    (H.laplacianCoefficients w s t e x r width) (fun i j => by
      simp [laplacianTable, laplacianCoefficients]) b
  rw [← determinant_value, (H.tabulated_laplacian_det w s t e x r).1] at h
  exact h

/-- On every tape, the algebraic evaluation of the reported sets uses coefficient vectors
of the chosen width. In particular width b+1 suffices for a nonnegative target b. -/
theorem parityEstimate_eq_coefficient_arrays {q width : ℕ} (e : Fin q ≃ {v // v ≠ s})
    (code : H.NonzeroCoeffs w s t ↪ CoinBlock (H.NonzeroCoeffs w s t)) (m : ℕ) (b : Fin width)
    (z : H.RandomMasks w s t × (Fin m → CoinBlock (H.NonzeroCoeffs w s t))) :
    H.parityEstimate w s t code m (b.val : ℤ) z =
      if 12*m < reports (H.coinFamily w s t code) z.1 z.2 then 0 else
      ∑ x ∈ covered (H.coinFamily w s t code) z.1 z.2,
        (determinant (H.laplacianCoefficients w s t e x z.1 width)).value.get b := by
  have hnonneg : ¬ (b.val : ℤ) < 0 := not_lt.mpr (Int.natCast_nonneg _)
  simp [parityEstimate, hnonneg, H.laplacian_coefficient, Polynomial.finsetSum_coeff]

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianParityDeterminant

section BoundedTrialCollection

/-! Stop a list of reporting trials at a global output limit. The extra report detects overflow. -/

namespace BoundedEnumeration

variable {U : Type*}

variable (trial : U → ℕ → Result) (allWords : U → List (List Bool))

variable (spec : ∀ u cap, (trial u cap).words = (allWords u).take cap)

include spec in
theorem collect_words (us : List U) (cap : ℕ) :
    (collect trial us cap).words =
      if (us.flatMap allWords).length ≤ cap then some (us.flatMap allWords) else none := by
  induction us generalizing cap with
  | nil => simp [collect]
  | cons u us ih =>
    by_cases h : (allWords u).length ≤ cap
    · have ht := List.take_of_length_le (l := allWords u) (show (allWords u).length ≤ cap+1 by omega)
      simp only [collect, spec, ht, Nat.not_lt.mpr h, if_false, ih, List.flatMap_cons, List.length_append]
      by_cases hs : (us.flatMap allWords).length ≤ cap-(allWords u).length
      · rw [if_pos hs, if_pos (show (allWords u).length + (us.flatMap allWords).length ≤ cap by omega)]
        rfl
      · rw [if_neg hs, if_neg (show ¬(allWords u).length + (us.flatMap allWords).length ≤ cap by omega)]
        rfl
    · have hcut : cap < min (cap+1) (allWords u).length := by omega
      have hfull : ¬ (allWords u).length + (us.flatMap allWords).length ≤ cap := by omega
      simp only [collect, spec, List.length_take, if_pos hcut, List.flatMap_cons, List.length_append, if_neg hfull]

end BoundedEnumeration

end BoundedTrialCollection

section HamiltonianAffineTrials

namespace DirectedHamiltonicity.Main.Multidigraph

open BoundedEnumeration AffinePrefixEnumeration FiniteSampling BirdDet.Tabulated

open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] {q N : ℕ}

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V) (order : Fin q ≃ Internal s t)

variable (rank : H.NonzeroCoeffs w s t ≃ Fin N) (r : H.RandomMasks w s t)

noncomputable def fullTrial (bits : CoinBlock (H.NonzeroCoeffs w s t)) : List (List Bool) :=
  match decodeRank rank bits with
  | none => []
  | some a => completions (accepts (H.samplingSystem w s t order r fun i => (a i).val)) q []

theorem affineTrial_spec (bits : CoinBlock (H.NonzeroCoeffs w s t)) (cap : ℕ) :
    (H.affineTrial w s t order rank r bits cap).words = (H.fullTrial w s t order rank r bits).take cap := by
  cases h : decodeRank rank bits with
  | none => simp [affineTrial, fullTrial, h]
  | some a => simpa [affineTrial, fullTrial, h] using
      (enumerate_spec (H.samplingSystem w s t order r fun i => (a i).val) cap).1

private theorem fullTrial_length (bits : CoinBlock (H.NonzeroCoeffs w s t)) :
    (H.fullTrial w s t order rank r bits).length = (H.coinFamily w s t (rankedCode rank) r bits).card := by
  rw [coinFamily, padded_eq_decode]
  cases h : decodeRank rank bits with
  | none => simp [fullTrial,h]
  | some a => simpa [fullTrial,h] using H.affine_trial_length w s t order r fun i => (a i).val

private theorem fullTrial_sets (bits : CoinBlock (H.NonzeroCoeffs w s t)) :
    (H.fullTrial w s t order rank r bits).toFinset.image (subsetOfBits s t order) =
      H.coinFamily w s t (rankedCode rank) r bits := by
  rw [coinFamily, padded_eq_decode]
  cases h : decodeRank rank bits with
  | none => simp [fullTrial,h]
  | some a =>
    simp only [fullTrial, h, Option.elim_some, H.affine_trial_words, Finset.image_image]
    simp [Function.comp_def, subsetOfBits]

theorem fullTape_length (m : ℕ) (tape : Fin m → CoinBlock (H.NonzeroCoeffs w s t)) :
    ((List.ofFn tape).flatMap (H.fullTrial w s t order rank r)).length =
      reports (H.coinFamily w s t (rankedCode rank)) r tape := by
  simp [List.length_flatMap,List.map_ofFn,Function.comp_def,List.sum_ofFn,H.fullTrial_length,reports]

theorem fullTape_sets (m : ℕ) (tape : Fin m → CoinBlock (H.NonzeroCoeffs w s t)) :
    ((List.ofFn tape).flatMap (H.fullTrial w s t order rank r)).toFinset.image (subsetOfBits s t order) =
      covered (H.coinFamily w s t (rankedCode rank)) r tape := by
  classical
  ext x
  simp only [covered,Finset.mem_biUnion,Finset.mem_univ,true_and,← H.fullTrial_sets w s t order rank r,
    Finset.mem_image,List.mem_toFinset,List.mem_flatMap,List.mem_ofFn]
  aesop

/-- The early stopping procedure either detects overflow or returns exactly the union of
reported subsets, including on unsuccessful random tapes. -/
theorem affine_collection_sets (m cap : ℕ) (tape : Fin m → CoinBlock (H.NonzeroCoeffs w s t)) :
    (collect (H.affineTrial w s t order rank r) (List.ofFn tape) cap).words.map
      (fun xs => xs.toFinset.image (subsetOfBits s t order)) =
        if reports (H.coinFamily w s t (rankedCode rank)) r tape ≤ cap
        then some (covered (H.coinFamily w s t (rankedCode rank)) r tape) else none := by
  classical
  let all := H.fullTrial w s t order rank r
  have hlen := H.fullTape_length w s t order rank r m tape
  have hsets := H.fullTape_sets w s t order rank r m tape
  change ((List.ofFn tape).flatMap all).length = _ at hlen
  change ((List.ofFn tape).flatMap all).toFinset.image (subsetOfBits s t order) = _ at hsets
  rw [collect_words _ all (H.affineTrial_spec w s t order rank r), hlen]
  split <;> simp_all

/-- For a nonnegative target that fits the chosen coefficient width, the finite estimator
equals the result of the capped searches followed by evaluation of the distinct subsets. -/
theorem parityEstimate_eq_affine_collection {p width : ℕ} (rows : Fin p ≃ {v // v ≠ s})
    (m : ℕ) (b : Fin width) (tape : Fin m → CoinBlock (H.NonzeroCoeffs w s t)) :
    let result := (collect (H.affineTrial w s t order rank r) (List.ofFn tape) (12*m)).words.map
      (fun xs => xs.toFinset.image (subsetOfBits s t order))
    H.parityEstimate w s t (rankedCode rank) m (b.val : ℤ) (r,tape) =
      result.elim 0 (fun sets => ∑ x ∈ sets, (determinant (H.laplacianCoefficients w s t rows x r width)).value.get b) := by
  dsimp only
  rw [H.affine_collection_sets, H.parityEstimate_eq_coefficient_arrays w s t rows]
  by_cases h : reports (H.coinFamily w s t (rankedCode rank)) r tape ≤ 12*m <;>
    simp [h, Nat.not_lt_of_ge, Nat.lt_of_not_ge]

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianAffineTrials

section HamiltonianRankedTrials

namespace DirectedHamiltonicity.Main.Multidigraph

open Classical BoundedEnumeration EditGV897.Main AffinePrefixEnumeration FiniteSampling

open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] {q N : ℕ}

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V) (order : Fin q ≃ Internal s t)

variable (rank : H.NonzeroCoeffs w s t ≃ Fin N) (r : H.RandomMasks w s t)

/-- The coefficient rank either supplies one affine system or marks an empty trial. -/
noncomputable def trialEquations (block : CoinBlock (H.NonzeroCoeffs w s t)) : Option (List (Equation q)) :=
  (decodeRank rank block).map fun a => H.samplingSystem w s t order r (fun i => (a i).val)

theorem wordsByRank_eq_full (block : CoinBlock (H.NonzeroCoeffs w s t)) :
    wordsByRank (H.trialEquations w s t order rank r block) = H.fullTrial w s t order rank r block := by
  cases h : decodeRank rank block <;> simp [trialEquations,h,fullTrial,wordsByRank,rankedSolutions_eq]

theorem fullTrial_width (block : CoinBlock (H.NonzeroCoeffs w s t)) (x : List Bool)
    (hx : x ∈ H.fullTrial w s t order rank r block) : x.length=q := by
  cases h : decodeRank rank block with
  | none => simp [fullTrial,h] at hx
  | some a =>
    simp only [fullTrial,h] at hx
    simpa only [List.length_nil,Nat.add_zero] using ((mem_completions ..).mp hx).1

theorem subsetOfBits_injective_on_words (x y : List Bool) (hx : x.length=q) (hy : y.length=q)
    (eq : subsetOfBits s t order x=subsetOfBits s t order y) : x=y := by
  have h := (numberedIndicator s t order).symm.injective eq
  simpa only [wordBits_bitsWord _ hx,wordBits_bitsWord _ hy] using congrArg wordBits h

/-- A first pass only adds the counts; an oversized tape returns zero. Otherwise
a second pass processes precisely the distinct reported words. This is the same
estimator on every tape, with no expectation in the time analysis. -/
theorem parityEstimate_ranked (m B : ℕ) (tape : Fin m → CoinBlock (H.NonzeroCoeffs w s t)) :
    let all := (List.ofFn tape).flatMap (fun bits => wordsByRank (H.trialEquations w s t order rank r bits))
    H.parityEstimate w s t (rankedCode rank) m (B : ℤ) (r,tape) =
      if all.length ≤ 12*m then ∑ x ∈ all.toFinset,
        (H.augLaplacian w s t (subsetOfBits s t order x) r).det.coeff B else 0 := by
  intro all
  let words := (List.ofFn tape).flatMap (H.fullTrial w s t order rank r)
  have agree : all=words := by simp [all,words,H.wordsByRank_eq_full]
  rw [agree]
  have len : words.length=reports (H.coinFamily w s t (rankedCode rank)) r tape :=
    H.fullTape_length w s t order rank r m tape
  have sets := H.fullTape_sets w s t order rank r m tape
  change words.toFinset.image (subsetOfBits s t order)=_ at sets
  have width (x : List Bool) (mem : x∈words.toFinset) : x.length=q := by
    obtain ⟨b,_,hx⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp mem)
    exact H.fullTrial_width w s t order rank r b x hx
  by_cases within : words.length ≤ 12*m
  · have safe : ¬ ((B:ℤ) < 0 ∨ 12*m < reports (H.coinFamily w s t (rankedCode rank)) r tape) := by omega
    rw [if_pos within,parityEstimate,if_neg safe,← sets,Polynomial.finsetSum_coeff,Int.toNat_natCast,Finset.sum_image]
    intro x hx y hy eq
    exact subsetOfBits_injective_on_words s t order x y (width _ hx) (width _ hy) eq
  · have fail : (B:ℤ) < 0 ∨ 12*m < reports (H.coinFamily w s t (rankedCode rank)) r tape := by omega
    rw [if_neg within,parityEstimate,if_pos fail]

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianRankedTrials

section HamiltonianRAMTrialProblem

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.BinaryStack AffinePrefixEnumeration EditGV897.Main FiniteSampling Multidigraph

namespace TrialParameters

abbrev row (P : TrialParameters) := rowArea P.bank

theorem denseWords_shape {q : ℕ} (E : List (Equation q)) :
    (denseWords E).length=E.length*(q+1) := by
  have rowLen (r : Equation q) : (rowPayload r).length=q+1 := by simp [rowPayload]
  induction E with
  | nil => simp [denseWords]
  | cons r E ih =>
    change ((r::E).flatMap rowPayload |>.map bitWord).length=_
    rw [List.flatMap_cons,List.map_append,List.length_append,List.length_map,rowLen]
    change (q+1)+(denseWords E).length=_
    rw [ih,List.length_cons,Nat.succ_mul,Nat.add_comm]

end TrialParameters

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMTrialProblem

section HamiltonianCappedRun

namespace TargetedSamplers.Structured

theorem applyPrefix_eq_foldl {X : Type*} (f : ℕ → X → X) (M : ℕ) (x : X) :
    applyPrefix f M x=(List.range M).foldl (fun v i => f i v) x := by
  induction M with
  | zero => rfl
  | succ M ih => simp [applyPrefix,List.range_succ,List.foldl_append,ih]

theorem prefixReports_length {α : Type*} (words : ℕ → List α) (M : ℕ) :
    prefixReports (fun i => (words i).length) M=((List.range M).flatMap words).length := by
  induction M with
  | zero => rfl
  | succ M ih => rw [prefixReports,ih,List.range_succ,List.flatMap_append,List.length_append];simp

theorem insert_all {α : Type*} [DecidableEq α] [Inhabited α] (xs : List α) (seen : Finset α) :
    applyPrefix (insertAt xs) xs.length seen=seen∪xs.toFinset := by
  have enum : (List.range xs.length).map (fun i => xs[i]?.getD default)=xs := by
    apply List.ext_getElem
    · simp
    · intro i hi hj;simp [List.getElem?_eq_getElem hj]
  have add (ys : List α) (base : Finset α) : ys.foldl (fun a v => insert v a) base=base∪ys.toFinset := by
    induction ys generalizing base with
    | nil => simp
    | cons y ys ih =>
      rw [List.foldl_cons,ih]
      ext z;simp [or_assoc,or_left_comm]
  rw [applyPrefix_eq_foldl]
  change (List.range xs.length).foldl (fun v i => insert (xs[i]?.getD default) v) seen=_
  have fold := congrArg (fun ys : List α => ys.foldl (fun v i => insert i v) seen) enum
  rw [List.foldl_map] at fold
  exact fold.trans (add xs seen)

theorem collect_reported_set {α : Type*} [DecidableEq α] [Inhabited α] (words : ℕ → List α) (M : ℕ) (s : Finset α) :
    applyPrefix (fun i => applyPrefix (insertAt (words i)) (words i).length) M s=
      s∪((List.range M).flatMap words).toFinset := by
  induction M with
  | zero => simp [applyPrefix]
  | succ M ih =>
    rw [applyPrefix,insert_all,ih,List.range_succ,List.flatMap_append,List.toFinset_append]
    simp [Finset.union_assoc]

end TargetedSamplers.Structured

namespace DirectedHamiltonicity.Main.Multidigraph

open FiniteSampling Classical EditGV897.Main TargetedSamplers.Structured

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] {q N : ℕ}

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V) (order : Fin q ≃ Internal s t)

variable (rank : H.NonzeroCoeffs w s t ≃ Fin N) (r : H.RandomMasks w s t)

noncomputable def trialAt (M : ℕ) (tape : Fin M → CoinBlock (H.NonzeroCoeffs w s t)) (i : ℕ) : List (List Bool) :=
  if hi : i < M then wordsByRank (H.trialEquations w s t order rank r (tape ⟨i,hi⟩)) else []

theorem trialAt_flat (M : ℕ) (tape : Fin M → CoinBlock (H.NonzeroCoeffs w s t)) :
    (List.range M).flatMap (H.trialAt w s t order rank r M tape)=
      (List.ofFn tape).flatMap (fun b => wordsByRank (H.trialEquations w s t order rank r b)) := by
  simp only [List.flatMap_def,List.map_ofFn]
  apply congrArg List.flatten
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h : i < M := by simpa using hi
    simp [trialAt,h]

theorem parity_as_capped_run (M B : ℕ) (tape : Fin M → CoinBlock (H.NonzeroCoeffs w s t)) :
    let words := H.trialAt w s t order rank r M tape
    let total := prefixReports (fun i => (words i).length) M
    let visited := applyPrefix (fun i => applyPrefix (insertAt (words i)) (words i).length) M ∅
    H.parityEstimate w s t (rankedCode rank) M (B:ℤ) (r,tape)=
      if total ≤ 12*M then ∑ x ∈ visited, (H.augLaplacian w s t (subsetOfBits s t order x) r).det.coeff B else 0 := by
  intro words total visited
  have count := prefixReports_length words M
  have seen := collect_reported_set words M ∅
  simp only [Finset.empty_union] at seen
  change _=if prefixReports (fun i => (words i).length) M ≤ 12*M then ∑ x ∈ visited, _ else 0
  change visited=_ at seen
  rw [count,seen,H.trialAt_flat w s t order rank r M tape]
  exact H.parityEstimate_ranked w s t order rank r M B tape

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianCappedRun

section HamiltonianRAMAlgorithm

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.BinaryStack AffinePrefixEnumeration FiniteSampling

def estimatorBody (bank c d : ℕ) (kernel counter : Cmd) : Cmd :=
  .seq (prepareRequest bank) (.seq (bootstrap bank c d kernel) (runTrials bank kernel counter))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMAlgorithm

section HamiltonianNativeGraph

namespace DirectedHamiltonicity.Main.NativeGraph

abbrev Graph := List (List (List Bool))

/-- Source and sink labels together with the normalized adjacency coefficient table. -/
abbrev Instance := Graph × (ℕ × ℕ)

def slots {α : Type} (xs : List α) : List ℕ := List.range xs.length

def labels (G : Graph) := slots G

def weights (G : Graph) : List ℕ := slots ((G.head?.getD []).head?.getD [])

def arc (G : Graph) (a v b : ℕ) : Bool := (((G[a]?.getD [])[v]?.getD [])[b]?).getD false

def internals (X : Instance) : List ℕ :=
  (labels X.1).filter fun v => !decide (v=X.2.1) && !decide (v=X.2.2)

def reduced (X : Instance) : List ℕ := (labels X.1).filter fun v => !decide (v=X.2.1)

def incoming (G : Graph) (v : ℕ) : List ℕ :=
  (weights G).filter fun b => !((labels G).filter fun a => arc G a v b).isEmpty

def before (xs : List ℕ) (j : ℕ) : List ℕ := xs.filter fun i => decide (i < j)

def bit (z i : ℕ) := z.bits[i]?.getD false

def parity (xs : List Bool) := (xs.filter id).length.bodd

def product (ns : List ℕ) : ℕ := ((ns.map fun x : ℕ => (x : ℚ)).prod).num.natAbs

theorem product_eq (xs : List ℕ) : product xs=xs.prod := by
  have cast : (xs.map fun x : ℕ => (x : ℚ)).prod=(xs.prod : ℚ) := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp only [List.map_cons,List.prod_cons,Nat.cast_mul,ih]
  rw [product,cast,Rat.num_natCast,Int.natAbs_natCast]

def radix (G : Graph) (v : ℕ) : ℕ := product ((0::incoming G v).map fun _ => 2)-1

theorem radix_eq (G : Graph) (v : ℕ) : radix G v=2^((incoming G v).length+1)-1 := by
  rw [radix,product_eq,List.map_const',List.prod_replicate,List.length_cons]

def earlierWeights (X : Instance) (v : ℕ) : List ℕ :=
  (before (internals X) v).flatMap fun u => incoming X.1 u

def maskLength (X : Instance) : ℕ := ((internals X).flatMap (incoming X.1)).length

def rankCard (X : Instance) : ℕ := product ((internals X).map (radix X.1))

def maskBit (X : Instance) (mask v b : ℕ) : Bool :=
  bit mask ((earlierWeights X v).length+(before (incoming X.1 v) b).length)

def rowWord (X : Instance) (rank v : ℕ) : ℕ :=
  (rank / product ((before (internals X) v).map (radix X.1))) % radix X.1 v + 1

def present (G : Graph) (v b : ℕ) : Bool := !((incoming G v).filter (fun k => decide (k=b))).isEmpty

def internal (X : Instance) (v : ℕ) := !decide (v=X.2.1) && !decide (v=X.2.2)

def active (X : Instance) (word a : ℕ) : Bool :=
  !(internal X a) || bit word (before (internals X) a).length

def extra (X : Instance) (mask v b : ℕ) : Bool :=
  internal X v && present X.1 v b && maskBit X mask v b

/-- The coefficient of one augmented Laplacian entry. Each possible tail occurs once. -/
def coefficient (X : Instance) (mask word u v b : ℕ) : Bool :=
  parity ((labels X.1).map fun a =>
    (decide (u=v) || decide (a=u)) &&
      ((active X word a && arc X.1 a v b) || (decide (a=X.2.2) && extra X mask v b)))

def matrix (X : Instance) (mask word : ℕ) : Graph :=
  (reduced X).map fun u => (reduced X).map fun v => (weights X.1).map (coefficient X mask word u v)

/-- Evaluate a diagonal sampling equation at the empty set or a singleton.
The two cases need only a direct equality test for each tail during the scan. -/
def diagonal (X : Instance) (mask v b selected : ℕ) (hasSelected : Bool) : Bool :=
  parity ((labels X.1).map fun a =>
    ((!(internal X a) || (hasSelected && decide (a=selected))) && arc X.1 a v b) ||
      (decide (a=X.2.2) && extra X mask v b))

def evaluateRow (X : Instance) (mask rank v selected : ℕ) (hasSelected : Bool) : Bool :=
  let a := rowWord X rank v
  parity ((hasSelected && decide (v=selected) && bit a 0) ::
    (incoming X.1 v).map (fun b => bit a ((before (incoming X.1 v) b).length+1) && diagonal X mask v b selected hasSelected))

/-- The column after the last variable supplies the right-hand side. -/
def equationBit (X : Instance) (mask rank i j : ℕ) : Bool :=
  let vs := internals X
  let v := vs[i]?.getD 0
  let c := evaluateRow X mask rank v 0 false
  if j=vs.length then !c else xor c (evaluateRow X mask rank v (vs[j]?.getD 0) true)

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianNativeGraph

section HamiltonianWeightRanks

namespace DirectedHamiltonicity.Main.Multidigraph

open FiniteSampling

open scoped BigOperators

private def lowerIndices {α : Type} [Preorder α] {k : ℕ} (e : Fin k ≃o α) (x : α) :
    Fin (e.symm x).val ≃ {y : α // y < x} where
  toFun i := ⟨e (Fin.castLE (e.symm x).isLt.le i),by
    conv_rhs => rw [← e.apply_symm_apply x]
    exact e.strictMono i.isLt⟩
  invFun y := ⟨(e.symm y.val).val,e.symm.strictMono y.property⟩
  left_inv i := by apply Fin.ext; simp
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val

/-- The increasing index of a member is the number of strictly smaller members. -/
theorem sorted_rank {α : Type} [LinearOrder α] (A : Finset α) (x : A) :
    ((A.orderIsoOfFin rfl).symm x).val = (A.filter (· < x.val)).card := by
  let e := A.orderIsoOfFin rfl
  let trim : {y : A // y < x} ≃ ↥(A.filter (· < x.val)) :=
    { toFun := fun y => ⟨y.val.val,Finset.mem_filter.mpr ⟨y.val.property,y.property⟩⟩
      invFun := fun y => ⟨⟨y.val,(Finset.mem_filter.mp y.property).1⟩,(Finset.mem_filter.mp y.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_congr ((lowerIndices e x).trans trim)

variable {n : ℕ} {E : Type} [Fintype E] (H : Multidigraph (Fin n) E) (w : E → ℕ) (s t : Fin n)

theorem weightColumns_some (v : Fin n) (b : H.incomingWeights w v) :
    (H.weightColumns w v (some b)).val = ((H.incomingWeights w v).filter (· < b.val)).card+1 := by
  change (((H.incomingWeights w v).orderIsoOfFin rfl).symm b).val + 1 = _
  rw [sorted_rank]

private theorem cast_weight_val {α : Type} (F : α → Finset ℕ) {x y : α}
    (he : x = y) (b : F x) : (he ▸ b : F y).val = b.val := by cases he; rfl

/-- The cumulative sizes of earlier internal rows and the number of smaller weights
in this row give the exact position on the shared random mask tape. -/
theorem orderedMaskIndex_val (i : Internal s t) (b : H.incomingWeights w i.val) :
    (H.orderedMaskIndex w s t ⟨i,b⟩).val =
      (∑ j : Fin (internalOrder s t i).val,
        (H.incomingWeights w ((internalOrder s t).symm (Fin.castLE (internalOrder s t i).isLt.le j)).val).card) +
        ((H.incomingWeights w i.val).filter (· < b.val)).card := by
  let e := internalOrder s t
  let N (j : Fin (internalLabels s t).card) := (H.incomingWeights w (e.symm j).val).card
  let J := e i
  have he : e.symm J = i := e.symm_apply_apply i
  let b' : H.incomingWeights w (e.symm J).val := he.symm ▸ b
  let z : (j : Fin (internalLabels s t).card) × Fin (N j) :=
    ⟨J,((H.incomingWeights w (e.symm J).val).orderIsoOfFin rfl).symm b'⟩
  have equiv : (H.orderedMaskIndex w s t ⟨i,b⟩).val = (finSigmaFinEquiv z).val := by rfl
  rw [equiv,finSigmaFinEquiv_apply]
  apply congrArg₂ (·+·) rfl
  dsimp only [z]
  rw [sorted_rank]
  change ((H.incomingWeights w (e.symm J).val).filter (· < b'.val)).card = _
  have hb : b'.val = b.val := cast_weight_val (fun v : Internal s t => H.incomingWeights w v.val) he.symm b
  rw [hb,he]

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianWeightRanks

section HamiltonianWeightedParity

namespace DirectedHamiltonicity.Main.Multidigraph

open FiniteSampling Polynomial Classical

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V) {W : ℕ} (hw : ∀ e, w e ≤ W)

omit [DecidableEq V] [DecidableEq E] in
theorem normalized_weightedPathCount_mod_two (B : ℤ) :
    ((H.normalizedGraph w s t hw).weightedPathCount (H.normalizedWeight w s t hw) s t B : ZMod 2) =
      (H.weightedPathCount w s t B : ZMod 2) := by
  classical
  let N := H.normalizedGraph w s t hw
  let p := H.normalizedWeight w s t hw
  by_cases hb : B < 0
  · have h₁ := H.weightedPathCount_eq_zero_outside w s t hw B (Or.inl hb)
    have h₂ := N.weightedPathCount_eq_zero_outside p s t (W := W)
      (fun a => Nat.le_of_lt_succ a.1.2.2.isLt) B (Or.inl hb)
    change (N.weightedPathCount p s t B : ZMod 2) = _
    rw [h₁, h₂]
  · have he := congrArg (fun f : Polynomial (ZMod 2) => f.coeff B.toNat)
        (H.normalizedGraph_pathPolynomial w s t hw)
    have hz : (B.toNat : ℤ) = B := Int.toNat_of_nonneg (le_of_not_gt hb)
    simpa only [coeff_hamPathPoly_monomials, hz] using he.symm

omit [DecidableEq E] in
/-- On every allowed weighted multigraph and every sufficiently long tape, the finite estimator
returns the requested Boolean parity with probability at least five sixths. The orderings used
by a concrete implementation may be chosen independently for each input. -/
theorem weightedParity_on_coin_tape (hst : s ≠ t) (B : ℤ) :
    let N := H.normalizedGraph w s t hw
    let p := H.normalizedWeight w s t hw
    let M := samplingBlockSize (Fintype.card V) (N.samplingDegree p) * (Fintype.card V + 4)
    ∀ (index : N.MaskIndex p s t ≃ Fin (Fintype.card (N.MaskIndex p s t)))
      (code : N.NonzeroCoeffs p s t ↪ CoinBlock (N.NonzeroCoeffs p s t))
      (L : ℕ) (hL : N.parityCoinCount p s t M ≤ L),
      5 / 6 ≤ probability (fun c : Fin L → Bool =>
        decide (N.parityEstimate p s t code M B
          (N.parityCoinBlocks p s t index M (fun i => c (Fin.castLE hL i))) ≠ 0) =
          decide (Odd (H.weightedPathCount w s t B))) := by
  intro N p M index code L hL
  have hp := N.parityEstimate_on_coin_tape p s t hst (H.normalizedGraph_isNormalized w s t hw)
    index code B L hL
  apply hp.trans
  apply probability_mono
  intro c hc
  have hc' := hc.trans (H.normalized_weightedPathCount_mod_two w s t hw B)
  have hbool (x : ZMod 2) (hx : x = (H.weightedPathCount w s t B : ZMod 2)) :
      decide (x ≠ 0) = decide (Odd (H.weightedPathCount w s t B)) := by
    subst x
    simp only [ZMod.natCast_ne_zero_iff_odd]
  exact hbool _ hc'

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianWeightedParity

section HamiltonianStreamedParity

namespace DirectedHamiltonicity.Main.Multidigraph

open FiniteSampling BoundedEnumeration BirdDet.Tabulated

open scoped BigOperators

variable {n : ℕ} {E : Type} [Fintype E] (H : Multidigraph (Fin n) E) (w : E → ℕ) (s t : Fin n)

/-- Equality holds on *every* tape, also after overflow, for targets outside the path-weight
range, and when the search misses a surviving set. -/
theorem streamedEstimate_eq {W : ℕ} (hw : ∀ e, w e ≤ W) (m : ℕ) (B : ℤ)
    (rest : List Bool) (r : H.RandomMasks w s t) (tape : Fin m → CoinBlock (H.NonzeroCoeffs w s t)) :
    H.streamedEstimate w s t W m (encInt B ++ rest) r tape =
      H.parityEstimate w s t (rankedCode (H.coefficientRank w s t)) m B (r,tape) := by
  unfold streamedEstimate
  rw [readTarget_encInt]
  by_cases hr : 0 ≤ B ∧ B ≤ (((n-1)*W : ℕ) : ℤ)
  · rw [if_pos hr]
    have he := H.parityEstimate_eq_affine_collection w s t (internalOrder s t).symm (H.coefficientRank w s t)
      r (reducedOrder s) m (⟨B.toNat,by omega⟩ : Fin (B.toNat+1)) tape
    simp only [Int.toNat_of_nonneg hr.1] at he
    change _ = _
    cases h : (collect (H.affineTrial w s t (internalOrder s t).symm (H.coefficientRank w s t) r)
      (List.ofFn tape) (12*m)).words <;> simpa [h] using he.symm
  · rw [if_neg hr]
    symm
    apply H.parityEstimate_zero_outside w s t hw
    simp only [Fintype.card_fin]
    omega

open Classical

/-- The concrete choices of row order, rank decoder, bounded searches and coefficient
arrays inherit the five-sixths guarantee on the original arbitrary multigraph. -/
theorem streamed_weightedParity_probability {W : ℕ} (hw : ∀ e, w e ≤ W) (hst : s ≠ t) (B : ℤ) :
    let G := H.normalizedGraph w s t hw
    let p := H.normalizedWeight w s t hw
    let m := samplingBlockSize n (G.samplingDegree p)*(n+4)
    ∀ L (hL : G.parityCoinCount p s t m ≤ L),
      5/6 ≤ probability (fun c : Fin L → Bool =>
        let z := G.parityCoinBlocks p s t (G.orderedMaskIndex p s t) m (fun i => c (Fin.castLE hL i))
        decide (G.streamedEstimate p s t W m (encInt B) z.1 z.2 ≠ 0) =
          decide (Odd (H.weightedPathCount w s t B))) := by
  intro G p m L hL
  have hp (a) : p a ≤ W := Nat.le_of_lt_succ a.1.2.2.isLt
  let law (j : ℕ) : Prop := ∀ (N : ℕ) (hn : G.parityCoinCount p s t j ≤ N),
    5/6 ≤ probability (fun c : Fin N → Bool =>
      decide (G.parityEstimate p s t (rankedCode (G.coefficientRank p s t)) j B
        (G.parityCoinBlocks p s t (G.orderedMaskIndex p s t) j (fun i => c (Fin.castLE hn i))) ≠ 0) =
        decide (Odd (H.weightedPathCount w s t B)))
  have hc : law (samplingBlockSize (Fintype.card (Fin n)) (G.samplingDegree p)*(Fintype.card (Fin n)+4)) :=
    H.weightedParity_on_coin_tape w s t hw hst B (G.orderedMaskIndex p s t) (rankedCode (G.coefficientRank p s t))
  have canonical : law m := by simpa only [Fintype.card_fin,m] using hc
  have hcopy := canonical L hL
  have he (r : G.RandomMasks p s t) (tape : Fin m → CoinBlock (G.NonzeroCoeffs p s t)) :
      G.streamedEstimate p s t W m (encInt B) r tape =
        G.parityEstimate p s t (rankedCode (G.coefficientRank p s t)) m B (r,tape) := by
    simpa only [List.append_nil] using G.streamedEstimate_eq p s t hp m B [] r tape
  simpa only [he, Prod.mk.eta] using hcopy

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianStreamedParity

section HamiltonianNativeGraphData

namespace DirectedHamiltonicity.Main.NativeGraph

open Multidigraph Classical

open scoped BigOperators

theorem bit_testBit (z i : ℕ) : bit z i=z.testBit i := by
  rw [Nat.testBit_eq_inth,List.getI_eq_getElem?_getD];rfl

/-- Scanning the labels in increasing order implements the order isomorphism used
to number a finite subset of the vertices. -/
theorem filtered_labels {n : ℕ} (A : Finset (Fin n)) (keep : ℕ → Bool)
    (test : ∀ a : Fin n, keep a.val=true ↔ a∈A) :
    (List.range n).filter keep = List.ofFn (fun i : Fin A.card => ((A.orderIsoOfFin rfl) i).val.val) := by
  let xs := (List.range n).filter keep
  have set : xs.toFinset=A.map Fin.valEmbedding := by
    ext z
    simp only [xs,List.mem_toFinset,List.mem_filter,List.mem_range,Finset.mem_map]
    constructor
    · rintro ⟨hz,h⟩;exact ⟨⟨z,hz⟩,(test _).mp h,rfl⟩
    · rintro ⟨a,ha,rfl⟩;exact ⟨a.isLt,(test a).mpr ha⟩
  have nodup : xs.Nodup := List.Nodup.filter keep List.nodup_range
  have sort : xs.toFinset.sort=xs := (List.toFinset_sort (·≤·) nodup).mpr (List.Pairwise.filter keep List.pairwise_le_range)
  have mapSort : (A.sort.map Fin.valEmbedding)=(A.map Fin.valEmbedding).sort :=
    Finset.map_sort Fin.valEmbedding A (·≤·) (·≤·) (fun _ _ _ _ => Iff.rfl)
  change xs=_
  rw [← sort,set,← mapSort]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [Finset.orderEmbOfFin_apply]

variable {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ) (hw : ∀ e, w e ≤ W) (s t : Fin n)

noncomputable def graphData : Graph := List.ofFn fun a : Fin n => List.ofFn fun v : Fin n =>
  List.ofFn fun b : Fin (W+1) => decide (H.retainArc w s t hw (a,v,b))

noncomputable def instanceData : Instance := (graphData H w hw s t,(s.val,t.val))

@[simp] theorem labels_data : labels (graphData H w hw s t)=List.range n := by simp [labels,slots,graphData]

@[simp] theorem weights_data : weights (graphData H w hw s t)=List.range (W+1) := by
  have pos : 0 < n := Nat.zero_lt_of_lt s.isLt
  cases n with
  | zero => omega
  | succ n => simp [weights,graphData,slots,List.ofFn_succ]

theorem arc_data (a v : Fin n) (b : Fin (W+1)) : arc (graphData H w hw s t) a.val v.val b.val =
    decide (H.retainArc w s t hw (a,v,b)) := by
  simp only [arc,graphData,List.getElem?_ofFn,dif_pos a.isLt,dif_pos v.isLt,dif_pos b.isLt,Option.getD_some]

theorem internals_data : internals (instanceData H w hw s t) =
    List.ofFn (fun i : Fin (internalLabels s t).card => ((internalOrder s t).symm i).val.val) := by
  unfold internals instanceData
  simp only [labels_data]
  apply filtered_labels (internalLabels s t)
  intro i
  simp [internalLabels,Fin.ext_iff]

theorem reduced_data : reduced (instanceData H w hw s t) =
    List.ofFn (fun i => (reducedOrder s i).val.val) := by
  unfold reduced instanceData
  simp only [labels_data]
  apply filtered_labels (Finset.univ.filter (fun i : Fin n => i ≠ s))
  intro i
  simp [Fin.ext_iff]

theorem incoming_mem (v : Fin n) (b : ℕ) :
    b∈incoming (graphData H w hw s t) v.val ↔
      b∈(H.normalizedGraph w s t hw).incomingWeights (H.normalizedWeight w s t hw) v := by
  let G := H.normalizedGraph w s t hw
  let p := H.normalizedWeight w s t hw
  have bounded : ∀ k∈G.incomingWeights p v, k < W+1 := by
    intro k hk
    obtain ⟨e,_,eq⟩ := Finset.mem_image.mp hk
    exact eq ▸ e.val.2.2.isLt
  simp only [incoming,List.mem_filter,weights_data,labels_data,List.mem_range,Bool.not_eq_true',List.isEmpty_eq_false_iff_exists_mem]
  constructor
  · rintro ⟨hb,existsTail⟩
    let k : Fin (W+1) := ⟨b,hb⟩
    apply (InputRAM.normalized_incoming_iff H w hw s t v k).mpr
    obtain ⟨a,ha,yes⟩ := existsTail
    let u : Fin n := ⟨a,ha⟩
    exact ⟨u,of_decide_eq_true ((arc_data H w hw s t u v k).symm.trans yes)⟩
  · intro hb
    let k : Fin (W+1) := ⟨b,bounded b hb⟩
    obtain ⟨a,yes⟩ := (InputRAM.normalized_incoming_iff H w hw s t v k).mp hb
    exact ⟨k.isLt,a.val,a.isLt,(arc_data H w hw s t a v k).trans (decide_eq_true yes)⟩

theorem incoming_set (v : Fin n) : (incoming (graphData H w hw s t) v.val).toFinset =
    (H.normalizedGraph w s t hw).incomingWeights (H.normalizedWeight w s t hw) v := by
  ext b;simpa only [List.mem_toFinset] using incoming_mem H w hw s t v b

theorem incoming_nodup (v : Fin n) : (incoming (graphData H w hw s t) v.val).Nodup := by
  unfold incoming
  rw [weights_data]
  exact List.Nodup.filter _ List.nodup_range

theorem incoming_length (v : Fin n) : (incoming (graphData H w hw s t) v.val).length =
    ((H.normalizedGraph w s t hw).incomingWeights (H.normalizedWeight w s t hw) v).card := by
  rw [← incoming_set, List.toFinset_card_of_nodup (incoming_nodup H w hw s t v)]

theorem before_card (xs : List ℕ) (h : xs.Nodup) (b : ℕ) :
    (before xs b).length=(xs.toFinset.filter (·<b)).card := by
  have same : (before xs b).toFinset=xs.toFinset.filter (·<b) := by ext i;simp [before]
  rw [← same]
  exact (List.toFinset_card_of_nodup (show (before xs b).Nodup from List.Nodup.filter _ h)).symm

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianNativeGraphData

section FiniteListPrefix

namespace FiniteSampling

/-- A strictly increasing enumeration lists every predecessor of its jth entry
in the first j positions, in exactly the order used by mixed-radix unranking. -/
theorem filtered_predecessors {n : ℕ} (f : Fin n → ℕ) (mono : StrictMono f) (j : Fin n) :
    (List.ofFn f).filter (fun x => decide (x < f j))=
      List.ofFn (fun h : Fin j.val => f (Fin.castLE j.isLt.le h)) := by
  let xs := List.ofFn f
  let p := fun x => decide (x < f j)
  have low : (xs.take j.val).filter p=xs.take j.val := by
    apply List.filter_eq_self.mpr
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ha
    simp only [p,List.getElem_take,xs,List.getElem_ofFn,decide_eq_true_eq]
    exact mono (show i < j.val from hi.trans_le (List.length_take_le ..))
  have high : (xs.drop j.val).filter p=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ha
    simp only [p,List.getElem_drop,xs,List.getElem_ofFn,decide_eq_true_eq]
    exact not_lt.mpr (mono.monotone (show j.val ≤ j.val+i by omega))
  calc
    _ = ((xs.take j.val)++(xs.drop j.val)).filter p := congrArg (List.filter p) (List.take_append_drop j.val xs).symm
    _ = xs.take j.val := by rw [List.filter_append,low,high,List.append_nil]
    _ = _ := by
      apply List.ext_getElem
      · simp [xs,Nat.min_eq_left j.isLt.le]
      · intro i left right;simp [xs,Fin.castLE]

end FiniteSampling

end FiniteListPrefix

section HamiltonianNativeRanks

namespace DirectedHamiltonicity.Main.NativeGraph

open Multidigraph FiniteSampling Classical

open scoped BigOperators

variable {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ)

variable (hw : ∀ e, w e ≤ W) (s t : Fin n)

local notation "G₀" => H.normalizedGraph w s t hw

local notation "w₀" => H.normalizedWeight w s t hw

local notation "A₀" => graphData H w hw s t

local notation "X₀" => instanceData H w hw s t

theorem before_internals_data (j : Fin (internalLabels s t).card) :
    before (internals X₀) ((internalOrder s t).symm j).val.val =
      List.ofFn (fun h : Fin j.val => ((internalOrder s t).symm (Fin.castLE j.isLt.le h)).val.val) := by
  rw [internals_data,before]
  refine filtered_predecessors (fun i : Fin (internalLabels s t).card => ((internalOrder s t).symm i).val.val) ?_ j
  intro i k hij
  exact ((internalLabels s t).orderIsoOfFin rfl).strictMono hij

theorem radix_data (i : Internal s t) : radix A₀ i.val.val=(G₀).coeffRadix w₀ s t i := by
  rw [radix_eq,incoming_length];rfl

theorem rankCard_data : rankCard X₀=(G₀).coeffRadixProduct w₀ s t := by
  rw [rankCard,internals_data,product_eq,List.map_ofFn,Fin.prod_ofFn]
  apply Finset.prod_congr rfl
  intro j _
  exact radix_data H w hw s t _

theorem maskLength_data : maskLength X₀=Fintype.card ((G₀).MaskIndex w₀ s t) := by
  rw [maskLength,internals_data,List.length_flatMap,List.map_ofFn,Fin.sum_ofFn,Fintype.card_sigma]
  calc
    _ = ∑ j : Fin (internalLabels s t).card, ((G₀).incomingWeights w₀ ((internalOrder s t).symm j).val).card := by
      apply Finset.sum_congr rfl
      intro j _
      exact incoming_length H w hw s t _
    _ = _ := by simpa only [Fintype.card_coe] using
          (internalOrder s t).symm.sum_comp (fun i => ((G₀).incomingWeights w₀ i.val).card)

theorem earlierWeights_data (j : Fin (internalLabels s t).card) :
    (earlierWeights X₀ ((internalOrder s t).symm j).val.val).length =
      ∑ h : Fin j.val, ((G₀).incomingWeights w₀ ((internalOrder s t).symm (Fin.castLE j.isLt.le h)).val).card := by
  rw [earlierWeights,before_internals_data,List.length_flatMap,List.map_ofFn,Fin.sum_ofFn]
  apply Finset.sum_congr rfl
  intro h _
  exact incoming_length H w hw s t _

theorem before_weight_data (v : Fin n) (b : ℕ) :
    (before (incoming A₀ v.val) b).length=(((G₀).incomingWeights w₀ v).filter (·<b)).card := by
  rw [before_card _ (incoming_nodup H w hw s t v),incoming_set]

/-- Positions of the shared tape bits agree with the sigma ordering for incident weights. -/
theorem maskBit_data (mask : ℕ) (i : Internal s t) (b : (G₀).incomingWeights w₀ i.val) :
    maskBit X₀ mask i.val.val b.val=mask.testBit ((G₀).orderedMaskIndex w₀ s t ⟨i,b⟩).val := by
  have earlier := earlierWeights_data H w hw s t (internalOrder s t i)
  simp only [Equiv.symm_apply_apply] at earlier
  rw [maskBit,bit_testBit,earlier,show (X₀).1=A₀ from rfl,before_weight_data H w hw s t i.val b.val,(G₀).orderedMaskIndex_val]

/-- A row uses all preceding radices exactly once and has a nonzero binary word. -/
theorem rowWord_data (a : (G₀).NonzeroCoeffs w₀ s t) (j : Fin (internalLabels s t).card) :
    let i := (internalOrder s t).symm j
    rowWord X₀ ((G₀).coefficientRank w₀ s t a).val i.val.val =
      (nonzeroRowRank ((G₀).weightColumns w₀ i.val) (a i)).val+1 := by
  intro i
  let e := internalOrder s t
  let rz := (G₀).coeffRadix w₀ s t
  let r := (G₀).coefficientRank w₀ s t
  let row := fun h : Internal s t => nonzeroRowRank ((G₀).weightColumns w₀ h.val)
  have val := tupleRank_digit e rz row (r a) j
  change (row i (r.symm (r a) i)).val=_ at val
  rw [Equiv.symm_apply_apply] at val
  have prefixProduct : product ((before (internals X₀) i.val.val).map (radix (X₀).1))=
      ∏ h : Fin j.val, rz (e.symm (Fin.castLE j.isLt.le h)) := by
    change product ((before (internals X₀) ((internalOrder s t).symm j).val.val).map (radix (X₀).1))=_
    rw [before_internals_data,product_eq,List.map_ofFn,Fin.prod_ofFn]
    apply Finset.prod_congr rfl
    intro h _
    exact radix_data H w hw s t _
  rw [rowWord,prefixProduct,show radix (X₀).1 i.val.val=rz i from radix_data H w hw s t i]
  exact congrArg (·+1) val.symm

private theorem bit_ranked_row {I : Type} {k : ℕ} (cols : I ≃ Fin k) (x : {f : I → Fin 2 // f ≠ 0}) (c : I) :
    bit ((nonzeroRowRank cols x).val+1) (cols c).val=finTwoEquiv (x.val c) := by
  have h := nonzeroRowRank_bit cols (nonzeroRowRank cols x) c
  rw [Equiv.symm_apply_apply] at h
  rw [bit_testBit,Nat.testBit_eq_decide_div_mod_eq,← h]
  exact (by decide : ∀ v : Fin 2, decide (v.val=1)=finTwoEquiv v) (x.val c)

private theorem rowWord_at_internal (a : (G₀).NonzeroCoeffs w₀ s t) (i : Internal s t) :
    rowWord X₀ ((G₀).coefficientRank w₀ s t a).val i.val.val =
      (nonzeroRowRank ((G₀).weightColumns w₀ i.val) (a i)).val+1 := by
  obtain ⟨j,rfl⟩ := (internalOrder s t).symm.surjective i
  exact rowWord_data H w hw s t a j

theorem rowWord_bit (a : (G₀).NonzeroCoeffs w₀ s t) (i : Internal s t) (c : Option ((G₀).incomingWeights w₀ i.val)) :
    bit (rowWord X₀ ((G₀).coefficientRank w₀ s t a).val i.val.val) ((G₀).weightColumns w₀ i.val c).val =
      finTwoEquiv ((a i).val c) := by
  rw [rowWord_at_internal H w hw s t a i]
  exact bit_ranked_row ((G₀).weightColumns w₀ i.val) (a i) c

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianNativeRanks

section HamiltonianLaplacianCoefficients

namespace DirectedHamiltonicity.Main.Multidigraph

open Polynomial Classical

open scoped BigOperators Polynomial

variable {V E : Type} [DecidableEq V] [Fintype E]

/-- The bit at a coefficient position uses one scan of the weighted edge table. -/
def coefficientEdges (G : Multidigraph V E) (w : E → ℕ) (u v : V) (k : ℕ) : Finset E :=
  Finset.univ.filter fun e => G.head e = v ∧ (u=v ∨ G.tail e=u) ∧ w e=k

private theorem sum_powers_coeff (es : Finset E) (w : E → ℕ) (k : ℕ) :
    (∑ e ∈ es, (X : (ZMod 2)[X])^(w e)).coeff k = ((es.filter (fun e => w e = k)).card : ZMod 2) := by
  simp [Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow,Finset.sum_boole,eq_comm]

theorem laplacian_coeff_eq_count (G : Multidigraph V E) (w : E → ℕ) (u v : V) (k : ℕ) :
    ((G.laplacian (fun e => (X : (ZMod 2)[X])^(w e))) u v).coeff k =
      ((G.coefficientEdges w u v k).card : ZMod 2) := by
  classical
  by_cases eq : u=v
  · subst v
    simp [laplacian,coefficientEdges,sum_powers_coeff,Finset.filter_filter,eq_comm]
  · simp [laplacian,eq,Polynomial.coeff_neg,sum_powers_coeff,ZMod.neg_eq_self_mod_two,coefficientEdges,
      Finset.filter_filter,and_assoc,and_left_comm,and_comm,eq_comm]

variable [Fintype V] (G : Multidigraph V E) (w : E → ℕ) (s t : V)

def weightXR (x : Finset (Internal s t)) (R : G.RandomMasks w s t) :
    ({e // G.KeepArc s t x e} ⊕ G.AugArc w s t R) → ℕ :=
  Sum.elim (fun e => w e.1) (fun a => a.2.1.1)

theorem augmented_coeff_eq_count (x : Finset (Internal s t)) (R : G.RandomMasks w s t)
    (u v : {v // v ≠ s}) (k : ℕ) :
    ((G.augLaplacian w s t x R) u v).coeff k =
      (((G.subXR w s t x R).coefficientEdges (G.weightXR w s t x R) u.val v.val k).card : ZMod 2) := by
  have label : G.subXRLabel w s t x R = fun e => (X : (ZMod 2)[X])^(G.weightXR w s t x R e) := by
    funext e; cases e <;> rfl
  change (((G.subXR w s t x R).laplacian (G.subXRLabel w s t x R)) u.val v.val).coeff k = _
  rw [label,laplacian_coeff_eq_count]

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianLaplacianCoefficients

section HamiltonianNormalizedLaplacian

namespace DirectedHamiltonicity.Main.Multidigraph

open Classical

open scoped BigOperators

variable {V E : Type} [DecidableEq V] [Fintype V] [Fintype E]

/-- In a graph with unique weighted triples, an entry coefficient can be counted
by scanning vertex labels at the prescribed head and weight. -/
theorem count_by_tail (H : Multidigraph V E) (w : E → ℕ)
    (unique : ∀ e f, H.tail e=H.tail f → H.head e=H.head f → w e=w f → e=f) (u v : V) (b : ℕ) :
    (H.coefficientEdges w u v b).card = (Finset.univ.filter fun a : V =>
      (u=v ∨ a=u) ∧ ∃ e, H.tail e=a ∧ H.head e=v ∧ w e=b).card := by
  classical
  let arcs := H.coefficientEdges w u v b
  have injective : Set.InjOn H.tail ↑arcs := by
    intro e he f hf tails
    obtain ⟨headE,_,wE⟩ := (Finset.mem_filter.mp he).2
    obtain ⟨headF,_,wF⟩ := (Finset.mem_filter.mp hf).2
    exact unique e f tails (headE.trans headF.symm) (wE.trans wF.symm)
  rw [← Finset.card_image_of_injOn (s := arcs) injective]
  apply congrArg Finset.card
  ext a
  simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,arcs,coefficientEdges]
  constructor
  · rintro ⟨e,⟨he,matchRow,weight⟩,rfl⟩
    exact ⟨matchRow,e,rfl,he,weight⟩
  · rintro ⟨matchRow,e,rfl,head,weight⟩
    exact ⟨e,⟨head,matchRow,weight⟩,rfl⟩

def activeTail (s t : V) (x : Finset (Internal s t)) (a : V) : Prop :=
  ∀ h : a ≠ s ∧ a ≠ t, (⟨a,h⟩ : Internal s t) ∈ x

def maskAt (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (R : H.RandomMasks w s t) (v : V) (k : ℕ) : Prop :=
  ∃ i : Internal s t, i.val=v ∧ ∃ b ∈ R i, b.val=k

theorem maskAt_internal (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (R : H.RandomMasks w s t) (i : Internal s t) (b : H.incomingWeights w i.val) :
    H.maskAt w s t R i.val b.val ↔ b ∈ R i := by
  constructor
  · rintro ⟨j,eq,c,mem,h⟩
    obtain rfl : j=i := Subtype.ext eq
    exact (Subtype.ext h : c=b) ▸ mem
  · intro h
    exact ⟨i,rfl,b,h,rfl⟩

private theorem augmented_unique (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (norm : H.IsNormalized w s t) (x : Finset (Internal s t)) (R : H.RandomMasks w s t) :
    let G := H.subXR w s t x R
    let p := H.weightXR w s t x R
    ∀ e f, G.tail e=G.tail f → G.head e=G.head f → p e=p f → e=f := by
  intro G p e f ht hh hw
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      apply congrArg Sum.inl
      apply Subtype.ext
      by_contra h
      exact norm.2.2.2 e.val f.val h ht hh hw
    | inr f => exact (norm.2.2.1 e.val ht).elim
  | inr e =>
    cases f with
    | inl f => exact (norm.2.2.1 f.val ht.symm).elim
    | inr f =>
      obtain ⟨i,b⟩ := e
      obtain ⟨j,c⟩ := f
      change i.val=j.val at hh
      obtain rfl : i=j := Subtype.ext hh
      apply congrArg Sum.inr
      apply congrArg (Sigma.mk _)
      exact Subtype.ext (Subtype.ext hw)

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V) {W : ℕ} (hw : ∀ e, w e ≤ W)

theorem augmented_present (x : Finset (Internal s t))
    (R : (H.normalizedGraph w s t hw).RandomMasks (H.normalizedWeight w s t hw) s t)
    (a v : V) (k : Fin (W+1)) :
    let G := H.normalizedGraph w s t hw
    let p := H.normalizedWeight w s t hw
    let A := G.subXR p s t x R
    (∃ e, A.tail e=a ∧ A.head e=v ∧ G.weightXR p s t x R e=k.val) ↔
      (activeTail s t x a ∧ H.retainArc w s t hw (a,v,k)) ∨
      (a=t ∧ G.maskAt p s t R v k.val) := by
  intro G p A
  constructor
  · rintro ⟨e,ht,hh,weight⟩
    cases e with
    | inl e =>
      change e.val.val.1=a at ht
      change e.val.val.2.1=v at hh
      change e.val.val.2.2.val=k.val at weight
      have key : e.val.val=(a,v,k) := Prod.ext ht (Prod.ext hh (Fin.ext weight))
      exact Or.inl ⟨ht ▸ e.property,key ▸ e.val.property⟩
    | inr e => exact Or.inr ⟨ht.symm,e.1,hh,e.2.val,e.2.property,weight⟩
  · rintro (⟨active,keep⟩|⟨rfl,i,head,b,keep,weight⟩)
    · let e : H.RetainedArc w s t hw := ⟨(a,v,k),keep⟩
      exact ⟨Sum.inl ⟨e,active⟩,rfl,rfl,rfl⟩
    · exact ⟨Sum.inr ⟨i,⟨b,keep⟩⟩,rfl,head,weight⟩

/-- The coefficient computed using the normalized adjacency bits, the candidate
vertex bits and the extra-arc mask. Both diagonal and off-diagonal cases use the
same scan, including the sink row and degree zero. -/
theorem normalized_coefficient (x : Finset (Internal s t))
    (R : (H.normalizedGraph w s t hw).RandomMasks (H.normalizedWeight w s t hw) s t)
    (u v : {v // v ≠ s}) (k : Fin (W+1)) :
    let G := H.normalizedGraph w s t hw
    let p := H.normalizedWeight w s t hw
    ((G.augLaplacian p s t x R) u v).coeff k.val =
      ((Finset.univ.filter (fun a : V => (u.val=v.val ∨ a=u.val) ∧
        ((activeTail s t x a ∧ H.retainArc w s t hw (a,v.val,k)) ∨
          (a=t ∧ G.maskAt p s t R v.val k.val)))).card : ZMod 2) := by
  intro G p
  rw [G.augmented_coeff_eq_count p s t x R u v k.val,count_by_tail _ _
    (augmented_unique G p s t (H.normalizedGraph_isNormalized w s t hw) x R)]
  apply congrArg (fun es : Finset V => (es.card : ZMod 2))
  ext a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact and_congr_right (fun _ => H.augmented_present w s t hw x R a v.val k)

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianNormalizedLaplacian

section HamiltonianNativeBitViews

namespace DirectedHamiltonicity.Main.NativeGraph

open Multidigraph FiniteSampling Classical TargetedSamplers.Structured.BinaryStack AffinePrefixEnumeration

theorem ranked_tape_bit {k : ℕ} (bits : Fin k → Bool) (i : Fin k) :
    (binaryRank k bits).val.testBit i.val=bits i := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have digit : (finTwoEquiv.symm (bits i)).val=((binaryRank k bits).val/2^i.val)%2 := by
    change _=((finFunctionFinEquiv.symm (finFunctionFinEquiv (fun a => finTwoEquiv.symm (bits a)))) i).val
    rw [Equiv.symm_apply_apply]
  rw [← digit]
  cases bits i <;> rfl

variable {n : ℕ} {E : Type} [Fintype E]

def CarriesMask (G : Multidigraph (Fin n) E) (p : E → ℕ) (s t : Fin n) (key : ℕ) (r : G.RandomMasks p s t) : Prop :=
  ∀ i : Internal s t, ∀ b : G.incomingWeights p i.val,
    key.testBit (G.orderedMaskIndex p s t ⟨i,b⟩).val = decide (b∈r i)

theorem carries_ranked_mask (G : Multidigraph (Fin n) E) (p : E → ℕ) (s t : Fin n)
    (bits : Fin (Fintype.card (G.MaskIndex p s t)) → Bool) :
    CarriesMask G p s t (binaryRank _ bits).val (G.masksOfBits p s t (G.orderedMaskIndex p s t) bits) := by
  intro i b
  rw [ranked_tape_bit]
  let J := G.orderedMaskIndex p s t
  change bits (J ⟨i,b⟩)=decide (b ∈ Finset.univ.filter (fun c => bits (J ⟨i,c⟩)=true))
  simp

def CarriesSubset (s t : Fin n) (key : ℕ) (x : Finset (Internal s t)) : Prop :=
  ∀ i : Internal s t, key.testBit (internalOrder s t i).val = decide (i∈x)

theorem carries_packed_subset (s t : Fin n) (word : List Bool) (length : word.length=(internalLabels s t).card) :
    CarriesSubset s t (packed word) (subsetOfBits s t (internalOrder s t).symm word) := by
  intro i
  let j := internalOrder s t i
  have hi : j.val < word.length := by rw [length];exact j.isLt
  rw [packed_testBit _ _ hi]
  have member : i∈subsetOfBits s t (internalOrder s t).symm word ↔ bitsWord _ word j ≠ 0 := by
    simp [subsetOfBits,numberedIndicator,j]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq,member]
  change word[j.val]=true ↔ (finTwoEquiv.symm (word[j.val]?.getD false) : ZMod 2) ≠ 0
  rw [List.getElem?_eq_getElem hi,Option.getD_some]
  cases word[j.val] <;> decide

variable {m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ)

variable (hw : ∀ e, w e ≤ W) (s t : Fin n)

local notation "G₀" => H.normalizedGraph w s t hw

local notation "w₀" => H.normalizedWeight w s t hw

local notation "A₀" => graphData H w hw s t

local notation "X₀" => instanceData H w hw s t

theorem internal_bool (v : Fin n) : internal X₀ v.val=decide (v ≠ s ∧ v ≠ t) := by
  apply Bool.eq_iff_iff.mpr
  by_cases hs : v.val=s.val <;> by_cases ht : v.val=t.val <;> simp [internal,instanceData,Fin.ext_iff,hs,ht]

theorem present_bool (v : Fin n) (b : ℕ) : present A₀ v.val b=decide (b∈(G₀).incomingWeights w₀ v) := by
  apply Bool.eq_iff_iff.mpr
  simp [present,List.isEmpty_eq_false_iff_exists_mem,incoming_mem H w hw s t]

theorem extra_iff (mask : ℕ) (r : (G₀).RandomMasks w₀ s t) (hm : CarriesMask G₀ w₀ s t mask r)
    (v : Fin n) (b : ℕ) : extra X₀ mask v.val b=true ↔ (G₀).maskAt w₀ s t r v b := by
  have necessary : (G₀).maskAt w₀ s t r v b → (v ≠ s ∧ v ≠ t) ∧ b∈(G₀).incomingWeights w₀ v := by
    rintro ⟨i,rfl,k,_,rfl⟩
    exact ⟨i.property,k.property⟩
  rw [extra,internal_bool,show (X₀).1=A₀ from rfl,present_bool H w hw s t v b]
  by_cases int : v ≠ s ∧ v ≠ t
  · by_cases has : b∈(G₀).incomingWeights w₀ v
    · let i : Internal s t := ⟨v,int⟩
      let k : (G₀).incomingWeights w₀ i.val := ⟨b,has⟩
      have val := (maskBit_data H w hw s t mask i k).trans (hm i k)
      have spec := (G₀).maskAt_internal w₀ s t r i k
      have raw : maskBit X₀ mask v.val b=decide (k∈r i) := val
      rw [raw,Bool.and_eq_true,Bool.and_eq_true]
      exact ⟨fun h => spec.mpr (of_decide_eq_true h.2),fun h =>
        ⟨⟨decide_eq_true int,decide_eq_true has⟩,decide_eq_true (spec.mp h)⟩⟩
    · have absent : ¬ (G₀).maskAt w₀ s t r v b := fun h => has (necessary h).2
      simp [has,absent]
  · have absent : ¬ (G₀).maskAt w₀ s t r v b := fun h => int (necessary h).1
    simp [int,absent]

theorem active_iff (key : ℕ) (x : Finset (Internal s t)) (hx : CarriesSubset s t key x) (a : Fin n) :
    active X₀ key a.val=true ↔ activeTail s t x a := by
  rw [active,internal_bool]
  by_cases yes : a ≠ s ∧ a ≠ t
  · let i : Internal s t := ⟨a,yes⟩
    have prefixSize := congrArg List.length (before_internals_data H w hw s t (internalOrder s t i))
    simp only [Equiv.symm_apply_apply,List.length_ofFn] at prefixSize
    change (before (internals X₀) a.val).length=(internalOrder s t i).val at prefixSize
    rw [prefixSize,bit_testBit,hx i]
    simp [activeTail,i,yes]
  · simp [activeTail,yes]

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianNativeBitViews

section HamiltonianRAMTapeView

namespace DirectedHamiltonicity.Main.Multidigraph

open FiniteSampling Classical EditGV897.Main AffinePrefixEnumeration TargetedSamplers.Structured

open TargetedSamplers.Structured.Word NativeGraph

variable {n : ℕ} {E : Type} [Fintype E] (G : Multidigraph (Fin n) E) (p : E → ℕ) (s t : Fin n)

noncomputable def inputCoins (M : ℕ) (coins : List Bool) :=
  G.parityCoinBlocks p s t (G.orderedMaskIndex p s t) M (fun k => coins[k.val]?.getD false)

def blockRank (coins : List Bool) (start width : ℕ) :=
  (binaryRank width (fun j => coins[start+j.val]?.getD false)).val

/-- The first random word supplies all node/weight masks, also on short tapes. -/
theorem inputCoins_mask (M : ℕ) (coins : List Bool) :
    CarriesMask G p s t (blockRank coins 0 (Fintype.card (G.MaskIndex p s t))) (G.inputCoins p s t M coins).1 := by
  let bits := fun j : Fin (Fintype.card (G.MaskIndex p s t)) => coins[j.val]?.getD false
  have first : (G.inputCoins p s t M coins).1=G.masksOfBits p s t (G.orderedMaskIndex p s t) bits := rfl
  rw [first]
  simpa only [blockRank,bits,Nat.zero_add] using carries_ranked_mask G p s t bits

theorem inputCoins_rank (M : ℕ) (coins : List Bool) (i : Fin M) :
    let length := Fintype.card (G.MaskIndex p s t)
    let width := Nat.clog 2 (Fintype.card (G.NonzeroCoeffs p s t))
    (binaryRank width ((G.inputCoins p s t M coins).2 i)).val=blockRank coins (length+width*i.val) width := by
  intro length width
  apply congrArg (fun x => (binaryRank width x).val)
  funext j
  exact trialBlocks_at length M width coins i j

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianRAMTapeView

section HamiltonianNativeParity

namespace DirectedHamiltonicity.Main.NativeGraph

open scoped BigOperators

def residue (b : Bool) : ZMod 2 := if b then 1 else 0

theorem residue_injective : Function.Injective residue := by
  intro a b;cases a <;> cases b <;> decide

theorem residue_nonzero (v : ZMod 2) : residue (decide (v ≠ 0))=v := by
  have cases₂ : ∀ x : ZMod 2, residue (decide (x ≠ 0))=x := by decide
  exact cases₂ v

theorem residue_and (a b : Bool) : residue (a && b)=residue a*residue b := by cases a <;> cases b <;> decide

theorem residue_xor (a b : Bool) : residue (xor a b)=residue a+residue b := by cases a <;> cases b <;> decide

theorem residue_not (a : Bool) : residue (!a)=1-residue a := by cases a <;> decide

theorem residue_parity (xs : List Bool) : residue (parity xs)=(xs.map residue).sum := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    have next : parity (b::xs)=xor b (parity xs) := by cases b <;> simp [parity]
    rw [next,residue_xor,ih,List.map_cons,List.sum_cons]

theorem range_parity (n : ℕ) (f : ℕ → Bool) (p : Fin n → Prop) [DecidablePred p]
    (h : ∀ a : Fin n, f a.val=true ↔ p a) :
    residue (parity ((List.range n).map f)) = ((Finset.univ.filter p).card : ZMod 2) := by
  have list : (List.range n).map f=List.ofFn (fun i : Fin n => f i.val) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi';simp
  rw [list,residue_parity,List.map_ofFn,Fin.sum_ofFn,Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro i _
  change (if f i.val=true then (1:ZMod 2) else 0)=_
  by_cases yes : p i
  · simp [yes,(h i).mpr yes]
  · simp [yes,mt (h i).mp yes]

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianNativeParity

section IntegerDeterminantInterpolation

/-! Coefficients of a polynomial determinant from a uniform integer determinant routine. -/

namespace IntegerDeterminantInterpolation

open Polynomial

open scoped BigOperators Polynomial

def evaluationMatrix (d : ℕ) : Matrix (Fin (d+1)) (Fin (d+1)) ℤ :=
  Matrix.vandermonde fun i => (i.val : ℤ)

theorem evaluationMatrix_det_ne_zero (d : ℕ) : (evaluationMatrix d).det ≠ 0 :=
  Matrix.det_vandermonde_ne_zero_iff.mpr (by
    intro i k eq
    apply Fin.ext
    change (i.val : ℤ) = (k.val : ℤ) at eq
    exact_mod_cast eq)

/-- Cramer's numerator is an exact integer multiple of the Vandermonde determinant. -/
theorem recover_mul (p : ℤ[X]) (d : ℕ) (hp : p.natDegree ≤ d) (j : Fin (d+1)) :
    ((evaluationMatrix d).updateCol j (fun i => p.eval (i.val:ℤ))).det =
      p.coeff j.val * (evaluationMatrix d).det := by
  let V := evaluationMatrix d
  have values : (fun i : Fin (d+1) => p.eval (i.val:ℤ)) =
      (fun k => ∑ h : Fin (d+1), p.coeff h.val • V k h) := by
    funext k
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp),← Fin.sum_univ_eq_sum_range]
    rfl
  change (V.updateCol j _).det = _
  rw [values,Matrix.det_updateCol_sum,smul_eq_mul]

/-- Evaluation determinants give an integer identity with no rounding. -/
theorem determinant_coeff_mul {n W : ℕ} (A : Matrix (Fin n) (Fin n) ℤ[X])
    (entries : ∀ i j, (A i j).natDegree ≤ W) (j : Fin (n*W+1)) :
    let V := evaluationMatrix (n*W)
    let y := fun i : Fin (n*W+1) => (A.map (fun p => p.eval (i.val:ℤ))).det
    (V.updateCol j y).det = A.det.coeff j.val * V.det := by
  intro V y
  have same : BirdDet.Tabulated.matrix (BirdDet.Tabulated.table A) = A :=
    Matrix.ext (fun i j => BirdDet.Tabulated.matrix_table A i j)
  have degree := BirdDet.Tabulated.determinant_degree (W := W) (BirdDet.Tabulated.table A)
    (by rw [same]; exact entries)
  rw [same] at degree
  have values : y = fun i : Fin (n*W+1) => A.det.eval (i.val:ℤ) := by
    funext i
    exact ((Polynomial.evalRingHom (i.val:ℤ)).map_det A).symm
  rw [values]
  exact recover_mul A.det _ degree j

/-- D+1 integer determinants supply all evaluations. Two more integer determinants
recover the requested coefficient by exact integer division. -/
theorem determinant_coeff {n W : ℕ} (A : Matrix (Fin n) (Fin n) ℤ[X])
    (entries : ∀ i j, (A i j).natDegree ≤ W) (j : Fin (n*W+1)) :
    let V := evaluationMatrix (n*W)
    let y := fun i : Fin (n*W+1) => (A.map (fun p => p.eval (i.val:ℤ))).det
    (V.updateCol j y).det / V.det = A.det.coeff j.val := by
  intro V y
  rw [show (V.updateCol j y).det = A.det.coeff j.val * V.det from determinant_coeff_mul A entries j]
  exact Int.mul_ediv_cancel _ (evaluationMatrix_det_ne_zero _)

end IntegerDeterminantInterpolation

end IntegerDeterminantInterpolation

section BinaryDeterminantInterpolation

namespace IntegerDeterminantInterpolation

open Polynomial

open scoped Polynomial BigOperators

/-- Lift the explicit coefficient row to integers before evaluating. -/
noncomputable def liftRow (W : ℕ) (p : (ZMod 2)[X]) : ℤ[X] :=
  ∑ i ∈ Finset.range (W+1), monomial i ((p.coeff i).val : ℤ)

theorem liftRow_degree (W : ℕ) (p : (ZMod 2)[X]) : (liftRow W p).natDegree ≤ W := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_monomial_le _).trans (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi)

theorem reduce_liftRow {W : ℕ} (p : (ZMod 2)[X]) (hp : p.natDegree ≤ W) :
    (liftRow W p).map (Int.castRingHom (ZMod 2)) = p := by
  conv_rhs => rw [p.as_sum_range' _ (Nat.lt_succ_of_le hp)]
  simp [liftRow,Polynomial.map_sum,Polynomial.map_monomial]

/-- A binary polynomial matrix is supplied as its table of entry coefficients.
Evaluations, interpolation and exact division are all over the integers. -/
theorem binary_determinant_coeff {n W : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)[X])
    (entries : ∀ i j, (A i j).natDegree ≤ W) (j : Fin (n*W+1)) :
    let B := A.map (liftRow W)
    let V := evaluationMatrix (n*W)
    let y := fun i : Fin (n*W+1) => (B.map (fun p => p.eval (i.val:ℤ))).det
    (((V.updateCol j y).det / V.det : ℤ) : ZMod 2) = A.det.coeff j.val := by
  intro B V y
  have h := determinant_coeff B (fun i k => liftRow_degree W (A i k)) j
  change (((V.updateCol j y).det / V.det : ℤ) : ZMod 2) = _
  rw [show (V.updateCol j y).det / V.det = B.det.coeff j.val from h]
  let φ := Polynomial.mapRingHom (Int.castRingHom (ZMod 2))
  have red : B.map φ = A := Matrix.ext fun a k => reduce_liftRow (A a k) (entries a k)
  have det : φ B.det = (B.map φ).det := φ.map_det B
  rw [red] at det
  simpa [φ,Polynomial.coeff_map] using congrArg (fun p : (ZMod 2)[X] => p.coeff j.val) det

end IntegerDeterminantInterpolation

end BinaryDeterminantInterpolation

section PolynomialDeterminantCoefficientLists

namespace IntegerDeterminantInterpolation.Native

abbrev CoeffTable := List (List (List Bool))

/-- Realize unary exponents by a product over a prefix of a list already in the input. -/
def power (u : (List ℕ × ℕ) × ℕ) : ℚ :=
  ((u.1.1.take u.2).map fun _ => (u.1.2 : ℚ)).prod

theorem power_eq (slots : List ℕ) (x k : ℕ) (h : k ≤ slots.length) :
    power ((slots,x),k) = (x:ℚ)^k := by
  simp [power,List.map_const,List.prod_replicate,min_eq_left h]

/-- For an n-square coefficient table of width W+1 this produces exactly 0,...,nW. -/
def points (A : CoeffTable) : List ℕ :=
  List.range (false :: A.flatMap (fun row => (row.head?.getD []).tail)).length

def evaluateEntry (p : List Bool × ℕ) : ℤ :=
  let slots := List.range p.1.length
  ((slots.map fun k => if p.1[k]?.getD false then power ((slots,p.2),k) else 0).sum).num

def evaluateRows (p : CoeffTable × ℕ) : List (List ℤ) :=
  p.1.map fun row => row.map fun c => evaluateEntry (c,p.2)

def vandermondeRows (slots : List ℕ) : List (List ℤ) :=
  slots.map fun i => slots.map fun k => (power ((slots,i),k)).num

def replacementRows (det : List (List ℤ) → ℤ) (p : CoeffTable × ℕ) : List (List ℤ) :=
  let slots := points p.1
  slots.map fun i =>
    let y := det (evaluateRows (p.1,i))
    slots.map fun k => if k=p.2 then y else (power ((slots,i),k)).num

def answer (det : List (List ℤ) → ℤ) (p : CoeffTable × ℕ) : Bool :=
  let num := det (replacementRows det p)
  let den := det (vandermondeRows (points p.1))
  decide ((((num:ℚ)/(den:ℚ)).num.natAbs % 2) = 1)

end IntegerDeterminantInterpolation.Native

end PolynomialDeterminantCoefficientLists

section NativeDeterminantCoefficientCorrect

namespace IntegerDeterminantInterpolation.Native

open Polynomial

open scoped BigOperators Polynomial

def entryWord (W : ℕ) (p : (ZMod 2)[X]) : List Bool :=
  List.ofFn fun k : Fin (W+1) => decide (p.coeff k.val ≠ 0)

def matrixRows {α : Type} {n : ℕ} (A : Matrix (Fin n) (Fin n) α) : List (List α) :=
  List.ofFn fun i => List.ofFn (A i)

def encodeTable {n : ℕ} (W : ℕ) (A : Matrix (Fin n) (Fin n) (ZMod 2)[X]) : CoeffTable :=
  matrixRows (A.map (entryWord W))

private theorem range_map_ofFn {α : Type} {n : ℕ} (f : ℕ → α) (g : Fin n → α)
    (h : ∀ i, f i.val = g i) : (List.range n).map f = List.ofFn g := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simpa using h ⟨i,by simpa using hi⟩

theorem evaluateEntry_word (W x : ℕ) (p : (ZMod 2)[X]) :
    evaluateEntry (entryWord W p,x) = (liftRow W p).eval (x:ℤ) := by
  let slots := List.range (W+1)
  let term (k : Fin (W+1)) := (((p.coeff k.val).val : ℚ) * (x:ℚ)^k.val)
  have vals : (slots.map (fun k => if (entryWord W p)[k]?.getD false then power ((slots,x),k) else 0)) =
      List.ofFn term := by
    apply range_map_ofFn
    intro k
    have idx : k.val < (entryWord W p).length := by simpa [entryWord] using k.isLt
    have pow := power_eq slots x k.val (by simpa [slots] using k.isLt.le)
    have lookup : (entryWord W p)[k.val] = decide (p.coeff k.val ≠ 0) := by simp only [entryWord,List.getElem_ofFn]
    rw [List.getElem?_eq_getElem idx,Option.getD_some,pow,lookup]
    simp only [decide_eq_true_eq]
    by_cases hz : p.coeff k.val = 0
    · rw [if_neg (not_not_intro hz)]
      simp only [term,hz,ZMod.val_zero,Nat.cast_zero,zero_mul]
    · have small := (p.coeff k.val).val_lt
      have nz : (p.coeff k.val).val ≠ 0 := fun h => hz ((ZMod.val_eq_zero _).mp h)
      have hv : (p.coeff k.val).val = 1 := by omega
      rw [if_pos hz]
      simp only [term,hv,Nat.cast_one,one_mul]
  have evaluation : (liftRow W p).eval (x:ℤ) =
      ∑ k : Fin (W+1), ((p.coeff k.val).val:ℤ)*(x:ℤ)^k.val := by
    rw [Fin.sum_univ_eq_sum_range (fun k => ((p.coeff k).val:ℤ)*(x:ℤ)^k)]
    simp only [liftRow,Polynomial.eval_finsetSum,Polynomial.eval_monomial]
  have rational : (∑ k, term k) = (((liftRow W p).eval (x:ℤ) : ℤ):ℚ) := by
    rw [evaluation]
    push_cast
    rfl
  unfold evaluateEntry
  simp only [entryWord,List.length_ofFn]
  change ((slots.map (fun k => if (entryWord W p)[k]?.getD false then power ((slots,x),k) else 0)).sum).num = _
  rw [vals,List.sum_ofFn,rational,Rat.num_intCast]

theorem points_table {n : ℕ} (W : ℕ) (A : Matrix (Fin n) (Fin n) (ZMod 2)[X]) :
    points (encodeTable W A) = List.range (n*W+1) := by
  cases n with
  | zero => simp [points,encodeTable,matrixRows]
  | succ n =>
    have rowLen (i : Fin (n+1)) :
        (((List.ofFn (fun j : Fin (n+1) => entryWord W (A i j))).head?.getD []).tail).length = W := by
      rw [List.ofFn_succ]
      simp [entryWord]
    unfold points encodeTable matrixRows
    congr 1
    simp [List.length_flatMap,List.map_ofFn,Function.comp_def,Matrix.map_apply,entryWord,List.sum_ofFn,Nat.succ_mul,add_comm]

theorem evaluateRows_table {n : ℕ} (W x : ℕ) (A : Matrix (Fin n) (Fin n) (ZMod 2)[X]) :
    evaluateRows (encodeTable W A,x) = matrixRows ((A.map (liftRow W)).map (fun p => p.eval (x:ℤ))) := by
  simp [evaluateRows,encodeTable,matrixRows,List.map_ofFn,Function.comp_def,Matrix.map_apply,evaluateEntry_word]
  rfl

private theorem power_num {D : ℕ} (i k : Fin (D+1)) :
    (power ((List.range (D+1),i.val),k.val)).num = (i.val:ℤ)^k.val := by
  rw [power_eq _ _ _ (by simpa using k.isLt.le)]
  have h : (i.val:ℚ)^k.val = (((i.val:ℤ)^k.val:ℤ):ℚ) := by norm_cast
  rw [h,Rat.num_intCast]

theorem vandermondeRows_range (D : ℕ) :
    vandermondeRows (List.range (D+1)) = matrixRows (evaluationMatrix D) := by
  apply range_map_ofFn
  intro i
  apply range_map_ofFn
  intro k
  exact power_num i k

private theorem replacement_table {n W : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)[X]) (j : Fin (n*W+1))
    (det : List (List ℤ) → ℤ) (correct : ∀ r (M : Matrix (Fin r) (Fin r) ℤ), det (matrixRows M) = M.det) :
    let B := A.map (liftRow W)
    let y := fun i : Fin (n*W+1) => (B.map (fun p => p.eval (i.val:ℤ))).det
    replacementRows det (encodeTable W A,j.val) = matrixRows ((evaluationMatrix (n*W)).updateCol j y) := by
  intro B y
  simp only [replacementRows,points_table]
  apply range_map_ofFn
  intro i
  apply range_map_ofFn
  intro k
  by_cases eq : k=j
  · subst k
    simp [evaluateRows_table,correct,Matrix.updateCol_self,y,B]
  · have neq : k.val ≠ j.val := fun h => eq (Fin.ext h)
    simp [neq,eq,Matrix.updateCol_ne,Matrix.updateCol_apply,power_num i k,Matrix.vandermonde,evaluationMatrix]

private theorem parity_natAbs (z : ℤ) : (z.natAbs%2 = 1) ↔ (z : ZMod 2) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have cast : (2:ℤ) ∣ z ↔ 2 ∣ z.natAbs := by
    rw [← Int.dvd_natAbs,← Int.natCast_dvd_natCast]
    norm_num
  change z.natAbs%2 = 1 ↔ ¬(2:ℤ) ∣ z
  rw [cast,Nat.dvd_iff_mod_eq_zero]
  omega

/-- Correctness on the actual list encoding, including the empty matrix and weight zero. -/
theorem answer_correct {n W : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)[X])
    (entries : ∀ i j, (A i j).natDegree ≤ W) (j : Fin (n*W+1))
    (det : List (List ℤ) → ℤ) (correct : ∀ r (M : Matrix (Fin r) (Fin r) ℤ), det (matrixRows M) = M.det) :
    answer det (encodeTable W A,j.val) = decide (A.det.coeff j.val ≠ 0) := by
  let B := A.map (liftRow W)
  let V := evaluationMatrix (n*W)
  let y := fun i : Fin (n*W+1) => (B.map (fun p => p.eval (i.val:ℤ))).det
  have hnum := determinant_coeff_mul B (fun i k => liftRow_degree W (A i k)) j
  have hz : V.det ≠ 0 := evaluationMatrix_det_ne_zero _
  have rat : (((V.updateCol j y).det : ℤ):ℚ) / (V.det:ℚ) = ((B.det.coeff j.val : ℤ):ℚ) := by
    apply (div_eq_iff (by exact_mod_cast hz)).mpr
    exact_mod_cast hnum
  have reduced := binary_determinant_coeff A entries j
  change (((V.updateCol j y).det / V.det : ℤ) : ZMod 2) = A.det.coeff j.val at reduced
  rw [show (V.updateCol j y).det = B.det.coeff j.val*V.det from hnum, Int.mul_ediv_cancel _ hz] at reduced
  unfold answer
  rw [replacement_table A j det correct,correct,points_table,vandermondeRows_range,correct]
  change decide (((((V.updateCol j y).det:ℚ) / (V.det:ℚ)).num.natAbs % 2) = 1) = _
  rw [rat,Rat.num_intCast]
  have eq : ((B.det.coeff j.val).natAbs % 2 = 1) ↔ A.det.coeff j.val ≠ 0 := (parity_natAbs _).trans (by rw [reduced])
  simp only [propext eq]

end IntegerDeterminantInterpolation.Native

end NativeDeterminantCoefficientCorrect

section HamiltonianNativeCoefficients

namespace DirectedHamiltonicity.Main.NativeGraph

open Multidigraph Classical IntegerDeterminantInterpolation.Native

open scoped BigOperators Polynomial

variable {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ)

variable (hw : ∀ e, w e ≤ W) (s t : Fin n)

local notation "G₀" => H.normalizedGraph w s t hw

local notation "w₀" => H.normalizedWeight w s t hw

local notation "A₀" => graphData H w hw s t

local notation "X₀" => instanceData H w hw s t

/-- This one coefficient scan is shared by the determinant and affine equations.
Its predicate may be supplied by a packed subset or by an empty/singleton query. -/
private theorem scan_coefficient (mask : ℕ) (r : (G₀).RandomMasks w₀ s t) (hm : CarriesMask G₀ w₀ s t mask r)
    (enabled : ℕ → Bool) (x : Finset (Internal s t)) (hx : ∀ a : Fin n, enabled a.val=true ↔ activeTail s t x a)
    (u v : {i : Fin n // i ≠ s}) (k : Fin (W+1)) :
    parity ((labels A₀).map fun a => (decide (u.val.val=v.val.val) || decide (a=u.val.val)) &&
      ((enabled a && arc A₀ a v.val.val k.val) ||
        (decide (a=t.val) && extra X₀ mask v.val.val k.val))) =
      decide ((((G₀).augLaplacian w₀ s t x r) u v).coeff k.val ≠ 0) := by
  apply residue_injective
  rw [residue_nonzero,H.normalized_coefficient w s t hw x r u v k,labels_data]
  apply range_parity
  intro a
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,hx,arc_data H w hw s t,
    extra_iff H w hw s t mask r hm,Fin.ext_iff]

theorem coefficient_data (mask key : ℕ) (r : (G₀).RandomMasks w₀ s t) (hm : CarriesMask G₀ w₀ s t mask r)
    (x : Finset (Internal s t)) (hx : CarriesSubset s t key x) (u v : {i : Fin n // i ≠ s}) (k : Fin (W+1)) :
    coefficient X₀ mask key u.val.val v.val.val k.val=
      decide ((((G₀).augLaplacian w₀ s t x r) u v).coeff k.val ≠ 0) :=
  scan_coefficient H w hw s t mask r hm _ x (active_iff H w hw s t key x hx) u v k

private theorem diagonal_entry {V E : Type} [Fintype V] [Fintype E] [dv : DecidableEq V]
    (G : Multidigraph V E) (p : E → ℕ) (s t : V) (x : Finset (Internal s t)) (r : G.RandomMasks p s t)
    (v : Internal s t) (k : G.incomingWeights p v.val) :
    G.diagCoeffs p s t x r v k=((G.augLaplacian p s t x r) ⟨v.val,v.property.1⟩ ⟨v.val,v.property.1⟩).coeff k.val := by
  have matrix_eq (d : DecidableEq V) :
      @Multidigraph.augLaplacian V E _ _ d G p s t x r=@Multidigraph.augLaplacian V E _ _ dv G p s t x r := by
    rw [Subsingleton.elim d dv]
  unfold Multidigraph.diagCoeffs
  exact congrArg (fun (A : Matrix {v : V // v ≠ s} {v : V // v ≠ s} (ZMod 2)[X]) =>
    (A ⟨v.val,v.property.1⟩ ⟨v.val,v.property.1⟩).coeff k.val) (matrix_eq _)

theorem diagonal_data (mask selected : ℕ) (hasSelected : Bool)
    (r : (G₀).RandomMasks w₀ s t) (hm : CarriesMask G₀ w₀ s t mask r) (x : Finset (Internal s t))
    (hx : ∀ a : Fin n, (!(internal X₀ a.val) || (hasSelected && decide (a.val=selected)))=true ↔ activeTail s t x a)
    (v : Internal s t) (k : (G₀).incomingWeights w₀ v.val) :
    diagonal X₀ mask v.val.val k.val selected hasSelected=decide ((G₀).diagCoeffs w₀ s t x r v k ≠ 0) := by
  have wt : k.val < W+1 := by
    obtain ⟨e,_,he⟩ := Finset.mem_image.mp k.property
    exact he ▸ e.val.2.2.isLt
  let i : {i : Fin n // i ≠ s} := ⟨v.val,v.property.1⟩
  have value := scan_coefficient H w hw s t mask r hm
    (fun j => !(internal X₀ j) || (hasSelected && decide (j=selected))) x hx i i ⟨k.val,wt⟩
  rw [diagonal_entry]
  have same : decide (i.val.val=i.val.val)=true := decide_eq_true rfl
  simpa only [diagonal,same,decide_true,Bool.true_or,Bool.true_and,i,show (X₀).1=A₀ from rfl,
    show (X₀).2.2=t.val from rfl] using value

theorem matrix_data (mask key : ℕ) (r : (G₀).RandomMasks w₀ s t) (hm : CarriesMask G₀ w₀ s t mask r)
    (x : Finset (Internal s t)) (hx : CarriesSubset s t key x) :
    matrix X₀ mask key=encodeTable W (((G₀).augLaplacian w₀ s t x r).submatrix (reducedOrder s) (reducedOrder s)) := by
  rw [matrix,reduced_data,show (X₀).1=A₀ from rfl,weights_data H w hw s t]
  simp only [List.map_ofFn,Function.comp_def,encodeTable,matrixRows,Matrix.map_apply,Matrix.submatrix_apply,entryWord]
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  apply List.ext_getElem
  · simp [IntegerDeterminantInterpolation.Native.entryWord]
  · intro j hi hj
    have bound : j < W+1 := by simpa using hi
    change ((List.range (W+1)).map (coefficient X₀ mask key ((reducedOrder s u).val.val) ((reducedOrder s v).val.val)))[j]=
      (IntegerDeterminantInterpolation.Native.entryWord W (((G₀).augLaplacian w₀ s t x r) (reducedOrder s u) (reducedOrder s v)))[j]
    simp only [IntegerDeterminantInterpolation.Native.entryWord,List.getElem_ofFn,List.getElem_map,List.getElem_range]
    exact coefficient_data H w hw s t mask key r hm x hx (reducedOrder s u) (reducedOrder s v) ⟨j,bound⟩

/-- The native integer determinant subroutine answers the exact bit used in the
parity estimator, including the constant coefficient and zero-weight graphs. -/
theorem determinant_bit (mask key : ℕ) (r : (G₀).RandomMasks w₀ s t) (hm : CarriesMask G₀ w₀ s t mask r)
    (x : Finset (Internal s t)) (hx : CarriesSubset s t key x)
    (j : Fin ((Finset.univ.filter (fun i : Fin n => i ≠ s)).card*W+1))
    (det : List (List ℤ) → ℤ) (correct : ∀ l (M : Matrix (Fin l) (Fin l) ℤ), det (matrixRows M)=M.det) :
    answer det (matrix X₀ mask key,j.val)=decide (((G₀).augLaplacian w₀ s t x r).det.coeff j.val ≠ 0) := by
  let A := ((G₀).augLaplacian w₀ s t x r).submatrix (reducedOrder s) (reducedOrder s)
  have entries (i k) : (A i k).natDegree ≤ W :=
    (G₀).augLaplacian_entry_degree w₀ s t (fun e => Nat.le_of_lt_succ e.val.2.2.isLt) x r _ _
  rw [matrix_data H w hw s t mask key r hm x hx,answer_correct A entries j det correct]
  simp [A,Matrix.det_submatrix_equiv_self]

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianNativeCoefficients

section HamiltonianSamplingEntries

namespace DirectedHamiltonicity.Main.Multidigraph

open Classical Matrix

open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E] (H : Multidigraph V E) (w : E → ℕ) (s t : V)

/-- Evaluate one sampling equation before moving its constant to the right-hand side. -/
noncomputable def rowAt (x : Finset (Internal s t)) (R : H.RandomMasks w s t)
    (a : (i : Internal s t) → H.CoeffVec w i.val) (i : Internal s t) : ZMod 2 :=
  a i none * (if i ∈ x then 1 else 0) + ∑ b, a i (some b)*H.diagCoeffs w s t x R i b

theorem rowAt_dot (x : Finset (Internal s t)) (R : H.RandomMasks w s t)
    (a : (i : Internal s t) → H.CoeffVec w i.val) (i : Internal s t) :
    H.samplingRow w s t R a i ⬝ᵥ liftedIndicator s t x = H.rowAt w s t x R a i := by
  classical
  simp only [samplingRow,add_dotProduct,sum_dotProduct,smul_dotProduct,single_dotProduct,one_mul,
    smul_eq_mul,diagonalForm_eval,rowAt,liftedIndicator]

theorem rowAt_empty (R : H.RandomMasks w s t) (a : (i : Internal s t) → H.CoeffVec w i.val)
    (i : Internal s t) : H.rowAt w s t ∅ R a i = H.samplingRow w s t R a i none := by
  classical
  rw [← H.rowAt_dot]
  simp [dotProduct,Fintype.sum_option,liftedIndicator]

theorem rowAt_singleton (R : H.RandomMasks w s t) (a : (i : Internal s t) → H.CoeffVec w i.val)
    (i j : Internal s t) : H.rowAt w s t {j} R a i =
      H.samplingRow w s t R a i none + H.samplingRow w s t R a i (some j) := by
  classical
  rw [← H.rowAt_dot]
  simp [dotProduct,Fintype.sum_option,liftedIndicator,mul_ite]

/-- The input rows for the Gaussian solver can use the same diagonal coefficient
evaluator as the determinant. The empty set gives the affine constant, and
differencing a singleton evaluation gives the associated matrix column. -/
theorem samplingSystem_by_diagonal {q : ℕ} (rows : Fin q ≃ Internal s t)
    (R : H.RandomMasks w s t) (a : (i : Internal s t) → H.CoeffVec w i.val) :
    H.samplingSystem w s t rows R a = List.ofFn (fun p : Fin q =>
      ((fun z : Fin q => H.rowAt w s t {rows z} R a (rows p) - H.rowAt w s t ∅ R a (rows p)),
        1-H.rowAt w s t ∅ R a (rows p))) := by
  classical
  simp [samplingSystem,H.rowAt_singleton,H.rowAt_empty]

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianSamplingEntries

section HamiltonianNativeEquations

namespace DirectedHamiltonicity.Main.NativeGraph

open Multidigraph Classical AffinePrefixEnumeration

open scoped BigOperators

variable {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ)

variable (hw : ∀ e, w e ≤ W) (s t : Fin n)

local notation "G₀" => H.normalizedGraph w s t hw

local notation "w₀" => H.normalizedWeight w s t hw

local notation "A₀" => graphData H w hw s t

local notation "X₀" => instanceData H w hw s t

local notation "Q" => Finset.card (internalLabels s t)

def selectedSet (z : Option (Internal s t)) : Finset (Internal s t) := z.elim ∅ fun i => {i}

def selectedLabel (z : Option (Internal s t)) : ℕ := z.elim 0 fun i => i.val.val

private theorem selected_tail (z : Option (Internal s t)) (a : Fin n) :
    (!(internal X₀ a.val) || (z.isSome && decide (a.val=selectedLabel s t z)))=true ↔
      activeTail s t (selectedSet s t z) a := by
  rw [internal_bool]
  by_cases hs : a.val=s.val <;> by_cases ht : a.val=t.val <;> cases z <;>
    simp [selectedLabel,selectedSet,activeTail,Subtype.ext_iff,Fin.ext_iff,hs,ht,decide_eq_true_eq] <;>
      exact ⟨of_decide_eq_true,decide_eq_true⟩

private theorem selected_indicator (z : Option (Internal s t)) (i : Internal s t) :
    residue (z.isSome && decide (i.val.val=selectedLabel s t z))=
      if i∈selectedSet s t z then 1 else 0 := by
  cases z with
  | none => simp [residue,selectedLabel,selectedSet]
  | some v =>
    by_cases e : i.val.val=v.val.val <;> simp [residue,selectedLabel,selectedSet,Subtype.ext_iff,Fin.ext_iff,e]

private theorem incoming_sum (v : Fin n) (f : ℕ → ZMod 2) :
    ((incoming A₀ v.val).map f).sum = ∑ b : (G₀).incomingWeights w₀ v, f b.val := by
  rw [← List.sum_toFinset f (incoming_nodup H w hw s t v),incoming_set,Finset.sum_coe_sort]

/-- The numerical dot product at the empty set and at a singleton is the same
affine functional used in the mathematical sampling theorem. -/
theorem evaluateRow_data (mask : ℕ) (r : (G₀).RandomMasks w₀ s t) (hm : CarriesMask G₀ w₀ s t mask r)
    (a : (G₀).NonzeroCoeffs w₀ s t) (i : Internal s t) (z : Option (Internal s t)) :
    residue (evaluateRow X₀ mask ((G₀).coefficientRank w₀ s t a).val i.val.val (selectedLabel s t z) z.isSome)=
      (G₀).rowAt w₀ s t (selectedSet s t z) r (fun h => (a h).val) i := by
  let row := rowWord X₀ ((G₀).coefficientRank w₀ s t a).val i.val.val
  let term (b : ℕ) := bit row ((before (incoming A₀ i.val.val) b).length+1) &&
    diagonal X₀ mask i.val.val b (selectedLabel s t z) z.isSome
  have alpha : bit row 0=finTwoEquiv ((a i).val none) := rowWord_bit H w hw s t a i none
  have coeff (v : ZMod 2) : residue (finTwoEquiv v)=v := (by decide : ∀ j : ZMod 2, residue (finTwoEquiv j)=j) v
  have weight (b : (G₀).incomingWeights w₀ i.val) : residue (term b.val)=
      (a i).val (some b)*(G₀).diagCoeffs w₀ s t (selectedSet s t z) r i b := by
    have col : (before (incoming A₀ i.val.val) b.val).length+1=((G₀).weightColumns w₀ i.val (some b)).val := by
      rw [before_weight_data,(G₀).weightColumns_some]
    dsimp only [term,row]
    rw [residue_and,col,rowWord_bit H w hw s t a i (some b),coeff ((a i).val (some b)),
      diagonal_data H w hw s t mask (selectedLabel s t z) z.isSome r hm (selectedSet s t z)
        (selected_tail H w hw s t z) i b,residue_nonzero]
  change residue (parity ((z.isSome && decide (i.val.val=selectedLabel s t z) && bit row 0)::
    (incoming A₀ i.val.val).map term))=_
  rw [residue_parity,List.map_cons,List.sum_cons,residue_and,alpha,coeff ((a i).val none),
    selected_indicator,List.map_map,incoming_sum]
  unfold rowAt
  congr 1
  · by_cases mem : i∈selectedSet s t z <;> simp only [if_pos,if_neg,mem,if_true,if_false,one_mul,mul_one,zero_mul,mul_zero]
  · exact Finset.sum_congr rfl (fun b _ => weight b)

private theorem internal_at (i : Fin Q) :
    (internals X₀)[i.val]?.getD 0=((internalOrder s t).symm i).val.val := by
  rw [internals_data]
  simp [List.getElem?_eq_getElem (by simpa using i.isLt : i.val < (List.ofFn
    (fun j : Fin Q => ((internalOrder s t).symm j).val.val)).length)]

theorem equation_rhs (mask : ℕ) (r : (G₀).RandomMasks w₀ s t) (hm : CarriesMask G₀ w₀ s t mask r)
    (a : (G₀).NonzeroCoeffs w₀ s t) (i : Fin Q) :
    residue (equationBit X₀ mask ((G₀).coefficientRank w₀ s t a).val i.val Q)=
      1-(G₀).rowAt w₀ s t ∅ r (fun h => (a h).val) ((internalOrder s t).symm i) := by
  have len : (internals X₀).length=Q := by rw [internals_data,List.length_ofFn]
  simp only [equationBit,len,if_pos rfl,if_true,internal_at H w hw s t i,residue_not]
  exact congrArg (fun x : ZMod 2 => 1-x) (evaluateRow_data H w hw s t mask r hm a _ none)

theorem equation_column (mask : ℕ) (r : (G₀).RandomMasks w₀ s t) (hm : CarriesMask G₀ w₀ s t mask r)
    (a : (G₀).NonzeroCoeffs w₀ s t) (i j : Fin Q) :
    residue (equationBit X₀ mask ((G₀).coefficientRank w₀ s t a).val i.val j.val)=
      (G₀).rowAt w₀ s t {((internalOrder s t).symm j)} r (fun h => (a h).val) ((internalOrder s t).symm i) -
      (G₀).rowAt w₀ s t ∅ r (fun h => (a h).val) ((internalOrder s t).symm i) := by
  have len : (internals X₀).length=Q := by rw [internals_data,List.length_ofFn]
  simp only [equationBit,len,if_neg (Nat.ne_of_lt j.isLt),internal_at H w hw s t i,internal_at H w hw s t j,residue_xor]
  have empty := evaluateRow_data H w hw s t mask r hm a ((internalOrder s t).symm i) none
  have singleton := evaluateRow_data H w hw s t mask r hm a ((internalOrder s t).symm i) (some ((internalOrder s t).symm j))
  dsimp only [selectedSet,selectedLabel,Option.elim,Option.isSome] at empty singleton
  rw [empty,singleton]
  exact (by decide : ∀ x y : ZMod 2, x+y=y-x) _ _

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianNativeEquations

section HamiltonianNativeTable

namespace AffinePrefixEnumeration

open EditGV897.Main

/-- Flattening a rectangular affine system uses the quotient for its row and
the remainder for its column. The last position of each row is the right-hand side. -/
theorem denseWords_rect {q h : ℕ} (E : Fin h → Equation q) (entry : ℕ → ℕ → Bool)
    (coef : ∀ (i : Fin h) (j : Fin q), entry i.val j.val=decide ((E i).1 j ≠ 0))
    (rhs : ∀ i : Fin h, entry i.val q=decide ((E i).2 ≠ 0)) :
    denseWords (List.ofFn E)=List.ofFn (fun k : Fin (h*(q+1)) => bitWord (entry (k.val/(q+1)) (k.val%(q+1)))) := by
  have row (i : Fin h) : (rowPayload (E i)).map bitWord=List.ofFn (fun j : Fin (q+1) => bitWord (entry i.val j.val)) := by
    rw [List.ofFn_succ' (fun j : Fin (q+1) => bitWord (entry i.val j.val)),List.concat_eq_append,rowPayload,
      List.map_append,List.map_ofFn,List.map_cons,List.map_nil]
    apply congrArg₂ (·++·)
    · apply congrArg List.ofFn
      funext j
      exact congrArg bitWord (coef i j).symm
    · exact congrArg (fun b => [bitWord b]) (rhs i).symm
  rw [List.ofFn_mul (fun k : Fin (h*(q+1)) => bitWord (entry (k.val/(q+1)) (k.val%(q+1))))]
  simp only [denseWords,List.flatMap_def,List.map_flatten,List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [row i]
  apply congrArg List.ofFn
  funext j
  have d : (i.val*(q+1)+j.val)/(q+1)=i.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (Nat.succ_pos _),Nat.div_eq_of_lt j.isLt,Nat.zero_add]
  simp only [d,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt j.isLt]

end AffinePrefixEnumeration

namespace DirectedHamiltonicity.Main.NativeGraph

open Multidigraph AffinePrefixEnumeration Classical

variable {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ)

variable (hw : ∀ e, w e ≤ W) (s t : Fin n)

local notation "G₀" => H.normalizedGraph w s t hw

local notation "w₀" => H.normalizedWeight w s t hw

local notation "X₀" => instanceData H w hw s t

local notation "Q" => Finset.card (internalLabels s t)

theorem equation_table (mask : ℕ) (r : (G₀).RandomMasks w₀ s t) (hm : CarriesMask G₀ w₀ s t mask r)
    (a : (G₀).NonzeroCoeffs w₀ s t) :
    denseWords ((G₀).samplingSystem w₀ s t (internalOrder s t).symm r (fun i => (a i).val))=
      List.ofFn (fun j : Fin (Q*(Q+1)) => bitWord (equationBit X₀ mask ((G₀).coefficientRank w₀ s t a).val
        (j.val/(Q+1)) (j.val%(Q+1)))) := by
  rw [(G₀).samplingSystem_by_diagonal]
  apply denseWords_rect
  · intro i j;apply residue_injective
    rw [residue_nonzero]
    exact equation_column H w hw s t mask r hm a i j
  · intro i;apply residue_injective
    rw [residue_nonzero]
    exact equation_rhs H w hw s t mask r hm a i

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianNativeTable

section NativeNumericFields

namespace TargetedSamplers.NumericFields

def read (radix : ℕ) : ℕ → ℕ → ℕ
  | 0,x => x%radix
  | i+1,x => read radix i (x/radix)

theorem read_join (radix : ℕ) (positive : 0 < radix) (xs : List ℕ) (bound : ∀ a∈xs,a < radix)
    (top i : ℕ) (hi : i < xs.length) : read radix i (join radix xs top)=xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    have small := bound x (by simp)
    cases i with
    | zero => simp [read,join,Nat.mod_eq_of_lt small]
    | succ i =>
      rw [read,join,Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt small,Nat.zero_add]
      exact ih (fun a ha => bound a (by simp [ha])) i (by simpa using hi)

theorem bounds (w : ℕ) (xs : List ℕ) (h : ∀ x∈xs,x < 2^w) :
    2^(w*xs.length) ≤ pack w xs ∧ pack w xs < 2^(w*xs.length+1) := by
  induction xs with
  | nil => simp [pack,join]
  | cons x xs ih =>
    have digit := h x (by simp)
    obtain ⟨low,high⟩ := ih (fun a ha => h a (by simp [ha]))
    have pos := Nat.two_pow_pos w
    have scaled := Nat.mul_le_mul_left (2^w) low
    have scaledTop := Nat.mul_le_mul_left (2^w) (Nat.succ_le_of_lt high)
    change _ ≤ x+2^w*pack w xs ∧ x+2^w*pack w xs < _
    rw [List.length_cons,Nat.mul_succ,Nat.add_comm (w*xs.length) w, pow_add,
      Nat.add_assoc w (w*xs.length) 1,pow_add]
    rw [Nat.mul_succ] at scaledTop
    omega

theorem pack_size (w : ℕ) (xs : List ℕ) (h : ∀ x∈xs,x < 2^w) : (pack w xs).size=w*xs.length+1 := by
  obtain ⟨lo,hi⟩ := bounds w xs h
  apply Nat.le_antisymm (Nat.size_le.mpr hi)
  by_contra! small
  have up := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : (pack w xs).size ≤ w*xs.length)
  have pos := Nat.lt_size_self (pack w xs)
  omega

end TargetedSamplers.NumericFields

end NativeNumericFields

section HamiltonianNativeRequest

namespace DirectedHamiltonicity.Main.NativeGraph

open TargetedSamplers.NumericFields

/-- Nine fixed-width fields encode n, W+1, source, sink, the adjacency bits, the
shared mask, the trial rank or candidate, the entry index or target, and the query kind. -/
def fieldWidth (z : ℕ) := (z.size-1)/9

def fieldBase (z : ℕ) := product ((z.bits.take (fieldWidth z)).map (fun _ => 2))

def field (i z : ℕ) := read (fieldBase z) i z

theorem fieldBase_eq (z : ℕ) : fieldBase z=2^(fieldWidth z) := by
  have short : fieldWidth z ≤ z.bits.length := by
    rw [Nat.size_eq_bits_len];exact (Nat.div_le_self ..).trans (Nat.sub_le ..)
  simp [fieldBase,product_eq,List.map_const',List.prod_replicate,Nat.min_eq_left short]

theorem field_pack (w : ℕ) (xs : List ℕ) (len : xs.length=9) (small : ∀ x∈xs,x < 2^w)
    (i : ℕ) (hi : i < 9) : field i (pack w xs)=xs[i]'(by omega) := by
  have width : fieldWidth (pack w xs)=w := by simp [fieldWidth,pack_size w xs small,len]
  rw [field,fieldBase_eq,width]
  exact read_join (2^w) (Nat.two_pow_pos _) xs small 1 i (by omega)

def requestLabels (z i : ℕ) : List ℕ := (slots z.bits).take (field i z)

def graphOfRequest (z : ℕ) : Graph :=
  let vs := requestLabels z 0
  let bs := requestLabels z 1
  vs.map fun a => vs.map fun v => bs.map fun b => bit (field 4 z) ((a*(field 0 z)+v)*(field 1 z)+b)

def instanceOfRequest (z : ℕ) : Instance := (graphOfRequest z,(field 2 z,field 3 z))

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianNativeRequest

section HamiltonianNativeGraphCost

namespace DirectedHamiltonicity.Main.NativeGraph

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

variable {I : Type} [Coding I] [Inhabited I]

@[local fun_prop] private theorem division {f g : I → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x/g x) := Poly.comp (f := fun a : ℕ × ℕ => a.1/a.2) ⟨PolyProgram.natDiv⟩ (Poly.pair hf hg)

@[local fun_prop] private theorem modulo {f g : I → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x%g x) := Poly.comp (f := fun a : ℕ × ℕ => a.1%a.2) ⟨PolyProgram.natMod⟩ (Poly.pair hf hg)

@[local fun_prop] private theorem boolXor {f g : I → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => xor (f x) (g x)) := Poly.comp (f := fun a : Bool × Bool => xor a.1 a.2)
      ⟨PolyProgram.boolXor⟩ (Poly.pair hf hg)

@[local fun_prop] private theorem sumN {f g : I → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x+g x) := Poly.comp Poly.nat_add (Poly.pair hf hg)

@[local fun_prop] private theorem subN {f g : I → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x-g x) := Poly.comp Poly.nat_sub (Poly.pair hf hg)

@[local fun_prop] private theorem andB {f g : I → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x && g x) := Poly.comp Poly.bool_and (Poly.pair hf hg)

@[local fun_prop] private theorem orB {f g : I → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x || g x) := Poly.comp Poly.bool_or (Poly.pair hf hg)

@[fun_prop] theorem slots_poly {α : Type} [Coding α] [Inhabited α] {f : I → List α} (hf : Poly f) :
    Poly (fun x => slots (f x)) := Poly.comp Poly.list_indices hf

@[fun_prop] theorem bit_poly {z i : I → ℕ} (hz : Poly z) (hi : Poly i) : Poly (fun x => bit (z x) (i x)) :=
  Poly.list_getD_comp false (Poly.comp (f := Nat.bits) ⟨PolyProgram.natAsList⟩ hz) hi

@[fun_prop] theorem parity_poly {f : I → List Bool} (hf : Poly f) : Poly (fun x => parity (f x)) :=
  Poly.comp (f := Nat.bodd) ⟨PolyProgram.natOdd⟩ (Poly.comp Poly.list_length
    (Poly.list_filter (f := fun (_ : I) b => b) Poly.snd hf))

@[fun_prop] theorem product_poly {f : I → List ℕ} (hf : Poly f) : Poly (fun x => product (f x)) :=
  Poly.comp (f := Int.natAbs) ⟨PolyProgram.intAbs⟩ (Poly.comp (f := Rat.num) ⟨PolyProgram.ratNum⟩
    (Poly.comp (f := (List.prod : List ℚ → ℚ)) ⟨PolyProgram.ratProd⟩
      (Poly.list_map (f := fun (_ : I) (n : ℕ) => (n:ℚ)) (Poly.comp Poly.rat_ofNat Poly.snd) hf)))

@[fun_prop] theorem labels_poly {G : I → Graph}
    (hG : Poly G) :
    Poly (fun x => labels (G x)) := by
  unfold labels
  fun_prop

@[fun_prop] theorem weights_poly {G : I → Graph}
    (hG : Poly G) :
    Poly (fun x => weights (G x)) := by
  unfold weights
  fun_prop

@[fun_prop] theorem arc_poly {G : I → Graph} {a v b : I → ℕ}
    (hG : Poly G) (ha : Poly a) (hv : Poly v) (hb : Poly b) :
    Poly (fun x => arc (G x) (a x) (v x) (b x)) := by
  unfold arc
  fun_prop

@[fun_prop] theorem internals_poly {X : I → Instance}
    (hX : Poly X) :
    Poly (fun x => internals (X x)) := by
  unfold internals
  fun_prop

@[fun_prop] theorem reduced_poly {X : I → Instance}
    (hX : Poly X) :
    Poly (fun x => reduced (X x)) := by
  unfold reduced
  fun_prop

@[fun_prop] theorem incoming_poly {G : I → Graph} {v : I → ℕ}
    (hG : Poly G) (hv : Poly v) :
    Poly (fun x => incoming (G x) (v x)) := by
  unfold incoming
  fun_prop

@[fun_prop] theorem before_poly {xs : I → List ℕ} {j : I → ℕ}
    (hxs : Poly xs) (hj : Poly j) :
    Poly (fun x => before (xs x) (j x)) := by
  unfold before
  fun_prop

@[fun_prop] theorem radix_poly {G : I → Graph} {v : I → ℕ}
    (hG : Poly G) (hv : Poly v) :
    Poly (fun x => radix (G x) (v x)) := by
  unfold radix
  fun_prop

@[fun_prop] theorem earlierWeights_poly {X : I → Instance} {v : I → ℕ}
    (hX : Poly X) (hv : Poly v) :
    Poly (fun x => earlierWeights (X x) (v x)) := by
  unfold earlierWeights
  fun_prop

@[fun_prop] theorem maskLength_poly {X : I → Instance}
    (hX : Poly X) :
    Poly (fun x => maskLength (X x)) := by
  unfold maskLength
  fun_prop

@[fun_prop] theorem rankCard_poly {X : I → Instance}
    (hX : Poly X) :
    Poly (fun x => rankCard (X x)) := by
  unfold rankCard
  fun_prop

@[fun_prop] theorem maskBit_poly {X : I → Instance} {mask v b : I → ℕ}
    (hX : Poly X) (hmask : Poly mask) (hv : Poly v) (hb : Poly b) :
    Poly (fun x => maskBit (X x) (mask x) (v x) (b x)) := by
  unfold maskBit
  fun_prop

@[fun_prop] theorem rowWord_poly {X : I → Instance} {r v : I → ℕ}
    (hX : Poly X) (hr : Poly r) (hv : Poly v) :
    Poly (fun x => rowWord (X x) (r x) (v x)) := by
  unfold rowWord
  fun_prop

@[fun_prop] theorem present_poly {G : I → Graph} {v b : I → ℕ}
    (hG : Poly G) (hv : Poly v) (hb : Poly b) :
    Poly (fun x => present (G x) (v x) (b x)) := by
  unfold present
  fun_prop

@[fun_prop] theorem internal_poly {X : I → Instance} {v : I → ℕ}
    (hX : Poly X) (hv : Poly v) :
    Poly (fun x => internal (X x) (v x)) := by
  unfold internal
  fun_prop

@[fun_prop] theorem active_poly {X : I → Instance} {w a : I → ℕ}
    (hX : Poly X) (hw : Poly w) (ha : Poly a) :
    Poly (fun x => active (X x) (w x) (a x)) := by
  unfold active
  fun_prop

@[fun_prop] theorem extra_poly {X : I → Instance} {mask v b : I → ℕ}
    (hX : Poly X) (hmask : Poly mask) (hv : Poly v) (hb : Poly b) :
    Poly (fun x => extra (X x) (mask x) (v x) (b x)) := by
  unfold extra
  fun_prop

@[fun_prop] theorem coefficient_poly {X : I → Instance} {mask w u v b : I → ℕ}
    (hX : Poly X) (hmask : Poly mask) (hw : Poly w) (hu : Poly u) (hv : Poly v) (hb : Poly b) :
    Poly (fun x => coefficient (X x) (mask x) (w x) (u x) (v x) (b x)) := by
  unfold coefficient
  fun_prop

@[fun_prop] theorem matrix_poly {X : I → Instance} {mask w : I → ℕ}
    (hX : Poly X) (hmask : Poly mask) (hw : Poly w) :
    Poly (fun x => matrix (X x) (mask x) (w x)) := by
  unfold matrix
  fun_prop

@[fun_prop] theorem diagonal_poly {X : I → Instance} {mask v b j : I → ℕ} {on : I → Bool}
    (hX : Poly X) (hmask : Poly mask) (hv : Poly v) (hb : Poly b) (hj : Poly j) (hon : Poly on) :
    Poly (fun x => diagonal (X x) (mask x) (v x) (b x) (j x) (on x)) := by
  unfold diagonal
  fun_prop

@[fun_prop] theorem evaluateRow_poly {X : I → Instance} {mask r v j : I → ℕ} {on : I → Bool}
    (hX : Poly X) (hmask : Poly mask) (hr : Poly r) (hv : Poly v) (hj : Poly j) (hon : Poly on) :
    Poly (fun x => evaluateRow (X x) (mask x) (r x) (v x) (j x) (on x)) := by
  unfold evaluateRow
  fun_prop

@[fun_prop] theorem equationBit_poly {X : I → Instance} {mask r i j : I → ℕ}
    (hX : Poly X) (hmask : Poly mask) (hr : Poly r) (hi : Poly i) (hj : Poly j) :
    Poly (fun x => equationBit (X x) (mask x) (r x) (i x) (j x)) := by
  unfold equationBit
  fun_prop

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianNativeGraphCost

section NativeDeterminantCoefficient

namespace IntegerDeterminantInterpolation.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Polynomial

open scoped BigOperators Polynomial

private theorem indices {α β : Type} [Coding α] [Coding β] [Inhabited β] {g : α → List β} (h : Poly g) :
    Poly (fun a => List.range (g a).length) := Poly.comp (f := fun xs : List β => List.range xs.length) (g := g) Poly.list_indices h

@[local fun_prop] private theorem ratProduct_poly : Poly (List.prod : List ℚ → ℚ) := ⟨PolyProgram.ratProd⟩

@[local fun_prop] private theorem num_poly : Poly Rat.num := ⟨PolyProgram.ratNum⟩

@[local fun_prop] private theorem abs_poly : Poly Int.natAbs := ⟨PolyProgram.intAbs⟩

@[local fun_prop] private theorem mod_poly : Poly (fun p : ℕ × ℕ => p.1%p.2) := ⟨PolyProgram.natMod⟩

@[fun_prop] theorem power_poly : Poly power := by
  unfold power
  apply Poly.comp ratProduct_poly
  apply Poly.list_map (f := fun (p : (List ℕ × ℕ) × ℕ) (_ : ℕ) => (p.1.2 : ℚ))
  · exact Poly.comp Poly.rat_ofNat (Poly.comp Poly.snd (Poly.comp Poly.fst Poly.fst))
  · exact Poly.comp QMCNumericRuntime.parser_take_poly (Poly.pair (Poly.comp Poly.fst Poly.fst) Poly.snd)

@[fun_prop] theorem points_poly : Poly points := by
  unfold points
  apply indices
  apply Poly.comp (g := fun a : CoeffTable => (false,a.flatMap fun row => (row.head?.getD []).tail)) Poly.list_cons
  apply Poly.pair (OAI.MetricKMedian.Binary.Automatic.Poly.const false)
  exact Poly.list_flatMap (f := fun (_ : CoeffTable) (row : List (List Bool)) => (row.head?.getD []).tail)
    (Poly.comp Poly.list_tail (Poly.comp (Poly.list_head []) Poly.snd)) Poly.identity

@[fun_prop] theorem evaluateEntry_poly : Poly evaluateEntry := by
  unfold evaluateEntry
  apply Poly.comp num_poly
  apply Poly.comp QMCNumericRuntime.rationalSum_poly
  apply Poly.list_map (f := fun (p : List Bool × ℕ) k =>
    if p.1[k]?.getD false then power ((List.range p.1.length,p.2),k) else 0)
  · apply Poly.ite
    · exact Poly.list_getD_comp false (Poly.comp Poly.fst Poly.fst) Poly.snd
    · exact Poly.comp power_poly (Poly.pair (Poly.pair (indices (g := fun x : (List Bool × ℕ) × ℕ => x.1.1) (Poly.comp Poly.fst Poly.fst))
        (Poly.comp Poly.snd Poly.fst)) Poly.snd)
    · exact OAI.MetricKMedian.Binary.Automatic.Poly.const 0
  · exact indices (g := (Prod.fst : List Bool × ℕ → List Bool)) Poly.fst

@[fun_prop] theorem evaluateRows_poly : Poly evaluateRows := by
  unfold evaluateRows
  apply Poly.list_map (as := (Prod.fst : CoeffTable × ℕ → CoeffTable))
    (f := fun (p : CoeffTable × ℕ) (row : List (List Bool)) => row.map fun c => evaluateEntry (c,p.2))
  · apply Poly.list_map (f := fun (w : (CoeffTable × ℕ) × List (List Bool)) c => evaluateEntry (c,w.1.2))
    · exact Poly.comp evaluateEntry_poly (Poly.pair Poly.snd (Poly.comp Poly.snd (Poly.comp Poly.fst Poly.fst)))
    · exact Poly.snd
  · exact Poly.fst

@[fun_prop] theorem vandermondeRows_poly : Poly vandermondeRows := by
  unfold vandermondeRows
  apply Poly.list_map (f := fun (slots : List ℕ) i => slots.map fun k => (power ((slots,i),k)).num)
  · exact Poly.list_map (f := fun (w : List ℕ × ℕ) k => (power (w,k)).num)
      (Poly.comp num_poly power_poly) Poly.fst
  · exact Poly.identity

@[fun_prop] theorem replacementRows_poly (det : List (List ℤ) → ℤ) (hd : Poly det) : Poly (replacementRows det) := by
  unfold replacementRows
  apply Poly.list_map (f := fun (p : CoeffTable × ℕ) i => (points p.1).map fun k =>
    if k=p.2 then det (evaluateRows (p.1,i)) else (power ((points p.1,i),k)).num)
  · apply Poly.list_map (f := fun (w : (CoeffTable × ℕ) × ℕ) k =>
      if k=w.1.2 then det (evaluateRows (w.1.1,w.2)) else (power ((points w.1.1,w.2),k)).num)
    · apply Poly.ite_prop
      · exact Poly.nat_eq_comp Poly.snd (Poly.comp Poly.snd (Poly.comp Poly.fst Poly.fst))
      · exact Poly.comp hd (Poly.comp evaluateRows_poly (Poly.pair (Poly.comp Poly.fst (Poly.comp Poly.fst Poly.fst))
          (Poly.comp Poly.snd Poly.fst)))
      · exact Poly.comp num_poly (Poly.comp power_poly (Poly.pair (Poly.pair
          (Poly.comp points_poly (Poly.comp Poly.fst (Poly.comp Poly.fst Poly.fst))) (Poly.comp Poly.snd Poly.fst)) Poly.snd))
    · exact Poly.comp points_poly (Poly.comp Poly.fst Poly.fst)
  · exact Poly.comp points_poly Poly.fst

theorem answer_poly (det : List (List ℤ) → ℤ) (hd : Poly det) : Poly (answer det) := by
  let num (x : CoeffTable × ℕ) : ℚ := det (replacementRows det x)
  let den (x : CoeffTable × ℕ) : ℚ := det (vandermondeRows (points x.1))
  have hn : Poly num := Poly.comp Poly.rat_ofInt (Poly.comp hd (replacementRows_poly det hd))
  have hd' : Poly den := Poly.comp Poly.rat_ofInt (Poly.comp hd (Poly.comp vandermondeRows_poly (Poly.comp points_poly Poly.fst)))
  have q : Poly (fun x => num x / den x) := Poly.comp (g := fun x => (num x,den x)) Poly.rat_div (Poly.pair hn hd')
  have a : Poly (fun x => (num x / den x).num.natAbs) := Poly.comp abs_poly (Poly.comp num_poly q)
  exact Poly.nat_eq_comp (Poly.comp (g := fun x => ((num x/den x).num.natAbs,2)) mod_poly
    (Poly.pair a (OAI.MetricKMedian.Binary.Automatic.Poly.const 2))) (OAI.MetricKMedian.Binary.Automatic.Poly.const 1)

end IntegerDeterminantInterpolation.Native

end NativeDeterminantCoefficient

section HamiltonianNativeRequestCost

namespace DirectedHamiltonicity.Main.NativeGraph

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TargetedSamplers.NumericFields IntegerDeterminantInterpolation.Native

def instanceAnswer (det : List (List ℤ) → ℤ) (X : Instance) (mask key index kind : ℕ) : ℕ :=
  if kind=0 then maskLength X else
  if kind=1 then rankCard X else
  if kind=2 then
    let stride := (internals X).length+1
    if equationBit X mask key (index/stride) (index%stride) then 2 else 1
  else if answer det (matrix X mask key,index) then 1 else 0

def respond (det : List (List ℤ) → ℤ) (z : ℕ) : ℕ :=
  instanceAnswer det (instanceOfRequest z) (field 5 z) (field 6 z) (field 7 z) (field 8 z)

variable {I : Type} [Coding I] [Inhabited I]

@[local fun_prop] private theorem divPoly {f g : I → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x/g x) :=
  Poly.comp (f := fun a : ℕ × ℕ => a.1/a.2) ⟨PolyProgram.natDiv⟩ (Poly.pair hf hg)

@[local fun_prop] private theorem modPoly {f g : I → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x%g x) :=
  Poly.comp (f := fun a : ℕ × ℕ => a.1%a.2) ⟨PolyProgram.natMod⟩ (Poly.pair hf hg)

@[local fun_prop] private theorem addPoly {f g : I → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x+g x) :=
  Poly.comp Poly.nat_add (Poly.pair hf hg)

@[local fun_prop] private theorem mulPoly {f g : I → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x*g x) :=
  Poly.comp Poly.nat_mul (Poly.pair hf hg)

@[local fun_prop] private theorem takePoly {α : Type} [Coding α] [Inhabited α] {f : I → List α}
    {g : I → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => (f x).take (g x)) :=
  Poly.comp (f := fun p : List α × ℕ => p.1.take p.2) ⟨PolyProgram.listTake enc default⟩ (Poly.pair hf hg)

@[local fun_prop] private theorem asBits {f : I → ℕ} (hf : Poly f) : Poly (fun x => (f x).bits) :=
  Poly.comp (f := Nat.bits) ⟨PolyProgram.natAsList⟩ hf

@[fun_prop] theorem fieldWidth_poly {f : I → ℕ} (hf : Poly f) : Poly (fun x => fieldWidth (f x)) :=
  divPoly (Poly.comp Poly.nat_sub (Poly.pair (Poly.comp (f := Nat.size) ⟨PolyProgram.natSize⟩ hf)
    (OAI.MetricKMedian.Binary.Automatic.Poly.const 1))) (OAI.MetricKMedian.Binary.Automatic.Poly.const 9)

@[fun_prop] theorem fieldBase_poly {f : I → ℕ} (hf : Poly f) : Poly (fun x => fieldBase (f x)) := by
  unfold fieldBase
  apply product_poly
  apply Poly.list_map (f := fun (_ : I) (_ : Bool) => (2:ℕ)) (OAI.MetricKMedian.Binary.Automatic.Poly.const 2)
  exact takePoly (asBits hf) (fieldWidth_poly hf)

private theorem read_poly (i : ℕ) {r f : I → ℕ} (hr : Poly r) (hf : Poly f) :
    Poly (fun x => read (r x) i (f x)) := by
  induction i generalizing f with
  | zero => exact modPoly hf hr
  | succ i ih => exact ih (divPoly hf hr)

@[fun_prop] theorem field_poly (i : ℕ) {f : I → ℕ} (hf : Poly f) : Poly (fun x => field i (f x)) :=
  read_poly i (fieldBase_poly hf) hf

@[fun_prop] theorem requestLabels_poly (i : ℕ) {f : I → ℕ} (hf : Poly f) : Poly (fun x => requestLabels (f x) i) :=
  takePoly (slots_poly (asBits hf)) (field_poly i hf)

@[fun_prop] theorem graphOfRequest_poly {f : I → ℕ} (hf : Poly f) : Poly (fun x => graphOfRequest (f x)) := by
  unfold graphOfRequest
  fun_prop

@[fun_prop] theorem instanceOfRequest_poly {f : I → ℕ} (hf : Poly f) : Poly (fun x => instanceOfRequest (f x)) :=
  Poly.pair (graphOfRequest_poly hf) (Poly.pair (field_poly 2 hf) (field_poly 3 hf))

theorem respond_poly (det : List (List ℤ) → ℤ) (fast : Poly det) : Poly (respond det) := by
  have coeff := answer_poly det fast
  unfold respond instanceAnswer
  fun_prop (disch := assumption)

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianNativeRequestCost

section HamiltonianGraphAnswers

namespace DirectedHamiltonicity.Main.NativeGraph

open Multidigraph AffinePrefixEnumeration Classical IntegerDeterminantInterpolation.Native

open scoped BigOperators

variable {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ)

variable (hw : ∀ e, w e ≤ W) (s t : Fin n)

local notation "G₀" => H.normalizedGraph w s t hw

local notation "w₀" => H.normalizedWeight w s t hw

local notation "X₀" => instanceData H w hw s t

local notation "Q" => Finset.card (internalLabels s t)

theorem mask_request (det : List (List ℤ) → ℤ) (m k j : ℕ) :
    instanceAnswer det X₀ m k j 0=Fintype.card ((G₀).MaskIndex w₀ s t) :=
  maskLength_data H w hw s t

theorem cardinality_request (det : List (List ℤ) → ℤ) (m k j : ℕ) :
    instanceAnswer det X₀ m k j 1=Fintype.card ((G₀).NonzeroCoeffs w₀ s t) :=
  (rankCard_data H w hw s t).trans ((G₀).coeffRadixProduct_eq_card w₀ s t)

theorem affine_request (det : List (List ℤ) → ℤ) (mask : ℕ) (r : (G₀).RandomMasks w₀ s t)
    (hm : CarriesMask G₀ w₀ s t mask r) (a : (G₀).NonzeroCoeffs w₀ s t) (i : Fin (Q*(Q+1))) :
    let E := (G₀).samplingSystem w₀ s t (internalOrder s t).symm r (fun j => (a j).val)
    instanceAnswer det X₀ mask ((G₀).coefficientRank w₀ s t a).val i.val 2 =
      (denseWords E)[i.val]?.getD 0 := by
  intro E
  have table := equation_table H w hw s t mask r hm a
  change denseWords E=_ at table
  have len : (internals X₀).length=Q := by rw [internals_data,List.length_ofFn]
  rw [table]
  change (if equationBit X₀ mask ((G₀).coefficientRank w₀ s t a).val
    (i.val/((internals X₀).length+1)) (i.val%((internals X₀).length+1)) then 2 else 1)=_
  rw [len]
  simp only [List.getElem?_ofFn,dif_pos i.isLt,Option.getD_some]
  let val := equationBit X₀ mask ((G₀).coefficientRank w₀ s t a).val (i.val/(Q+1)) (i.val%(Q+1))
  change (if val then 2 else 1)=bitWord val
  cases val <;> rfl

theorem leaf_request (det : List (List ℤ) → ℤ)
    (correct : ∀ l (M : Matrix (Fin l) (Fin l) ℤ), det (matrixRows M)=M.det)
    (mask key : ℕ) (r : (G₀).RandomMasks w₀ s t) (hm : CarriesMask G₀ w₀ s t mask r)
    (x : Finset (Internal s t)) (hx : CarriesSubset s t key x)
    (j : Fin ((Finset.univ.filter (fun i : Fin n => i ≠ s)).card*W+1)) :
    instanceAnswer det X₀ mask key j.val 3=
      (decide (((G₀).augLaplacian w₀ s t x r).det.coeff j.val ≠ 0)).toNat := by
  change (if answer det (matrix X₀ mask key,j.val) then 1 else 0)=_
  rw [determinant_bit H w hw s t mask key r hm x hx j det correct]
  cases decide (((G₀).augLaplacian w₀ s t x r).det.coeff j.val ≠ 0) <;> rfl

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianGraphAnswers

section HamiltonianParityRAM

namespace DirectedHamiltonicity.Main

open FiniteSampling Classical Multidigraph

/-- Realization of an estimator by a RAM program transfers its finite-tape success probability
to the published output law. The simulation may also say what happens on unsuccessful coins. -/
theorem outputProb_ge_estimator (P : TargetedSamplers.Program) (x : List Bool) (L : ℕ)
    (est : (Fin L → Bool) → Bool) (answer : Bool)
    (exec : ∀ c, P.Outputs (runTapes x (List.ofFn c)) (some [est c])) :
    probability (fun c => est c = answer) ≤ outputProb P x L [answer] := by
  classical
  let q := fun c : Fin L → Bool => P.Outputs (runTapes x (List.ofFn c)) (some [answer])
  have he : probability q = outputProb P x L [answer] := by
    simp only [probability_eq, outputProb, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    apply congrArg (fun S : Finset (Fin L → Bool) => (S.card : ℝ) / 2^L)
    ext c
    simp [q]
  apply (probability_mono (q := q) (fun c h => ?_)).trans_eq he
  change P.Outputs (runTapes x (List.ofFn c)) (some [answer])
  simpa only [h] using exec c

namespace Multidigraph

/-- The shared row masks and all disjoint trial blocks fit in a tape of the form required
by the public running-time statement, with constants independent of the degree. -/
theorem parity_coin_budget {n m W d : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ)
    (s t : Fin n) (hw : ∀ e, w e ≤ W) (hd : 1 ≤ d)
    (hdeg : ∀ v, (H.incomingWeights w v).card ≤ d) :
    let G := H.normalizedGraph w s t hw
    let w' := H.normalizedWeight w s t hw
    let M := samplingBlockSize n (G.samplingDegree w') * (n + 4)
    (G.parityCoinCount w' s t M : ℝ) ≤
      17 * (2 - (1 / 2 : ℝ)^d)^n * ((n + m + W + 1 : ℕ) : ℝ)^3 := by
  classical
  intro G w' M
  let b := (2 - (1/2 : ℝ)^d)^n
  let S : ℝ := (n + m + W + 1 : ℕ)
  have hS : 1 ≤ S := by dsimp [S]; exact_mod_cast (show 1 ≤ n + m + W + 1 by omega)
  have hn' : (n : ℝ) + 1 ≤ S := by dsimp [S]; exact_mod_cast (show n + 1 ≤ n + m + W + 1 by omega)
  have hn : (n : ℝ) ≤ S := by linarith
  have hm : (m : ℝ) + 1 ≤ S := by dsimp [S]; exact_mod_cast (show m + 1 ≤ n + m + W + 1 by omega)
  have hb : 1 ≤ b := by
    apply one_le_pow₀
    linarith [pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1/2 : ℝ) ≤ 1) (n := d)]
  have hdeg' (v : Fin n) : (G.incomingWeights w' v).card ≤ d :=
    (Finset.card_le_card (H.normalizedGraph_incomingWeights w s t hw v)).trans (hdeg v)
  have hM : (M : ℝ) ≤ 4 * (n + 4 : ℝ) * b := by
    simpa only [M, b, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using G.parity_trials_le w' d hd hdeg'
  have hE : Fintype.card (H.RetainedArc w s t hw) ≤ m := by
    simpa only [Fintype.card_fin] using H.normalizedGraph_card_le w s t hw
  have hbits : G.parityCoinCount w' s t M ≤ n * m + M * (n * (m + 1)) := by
    have h := G.parityCoinCount_le w' s t M
    rw [Fintype.card_fin] at h
    apply h.trans
    gcongr
  have hb' : 0 ≤ b := by linarith
  have hs' : 0 ≤ S := by linarith
  have hpart : (n : ℝ) * m ≤ b * S ^ 3 := by
    calc
      _ ≤ S * S := mul_le_mul hn (by linarith) (by positivity) hs'
      _ ≤ (S * S) * S := le_mul_of_one_le_right (by positivity) hS
      _ ≤ b * S^3 := by rw [show S * S * S = S^3 by ring]; exact le_mul_of_one_le_left (by positivity) hb
  have hmain : (M : ℝ) * (n * (m + 1 : ℝ)) ≤ 16 * b * S^3 := by
    calc
      _ ≤ (4 * (4*S) * b) * (S * S) := by
        have h₄ : (n : ℝ) + 4 ≤ 4 * S := by linarith
        have hM' := hM.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₄ (by norm_num : (0:ℝ) ≤ 4)) hb')
        exact mul_le_mul hM' (mul_le_mul hn hm (by positivity) hs') (by positivity) (by positivity)
      _ = _ := by ring
  change _ ≤ 17 * b * S^3
  have hreal : (G.parityCoinCount w' s t M : ℝ) ≤ (n : ℝ)*m + M*(n*(m+1 : ℝ)) := by exact_mod_cast hbits
  linarith

end Multidigraph

end DirectedHamiltonicity.Main

end HamiltonianParityRAM

section HamiltonianInputEstimator

namespace DirectedHamiltonicity.Main.Multidigraph

open Classical FiniteSampling

variable {n m : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ) (s t : Fin n)

private theorem coinAt_ofFn {L N : ℕ} (c : Fin L → Bool) (h : N ≤ L) :
    (fun i : Fin N => coinAt (List.ofFn c) i.val) = fun i => c (Fin.castLE h i) := by
  funext i
  have hl : i.val < (List.ofFn c).length := by simpa using i.isLt.trans_le h
  simp [coinAt,List.getElem?_eq_getElem hl,Fin.castLE]

set_option maxHeartbeats 1200000 in
/-- Uniform probability bound, with the parameters W and d appearing only in the resource
hypothesis. In particular the caller need not provide either of them to the estimator. -/
theorem inputEstimator_success {d W L : ℕ} (hd : 1 ≤ d) (hw : ∀ e, w e ≤ W)
    (hdeg : ∀ v, (H.incomingWeights w v).card ≤ d) (hst : s ≠ t) (B : ℤ)
    (hL : 17*(2-(1/2 : ℝ)^d)^n*((n+m+W+1 : ℕ) : ℝ)^3 ≤ L) :
    5/6 ≤ probability (fun c : Fin L → Bool => H.inputEstimator w s t (encInt B) (List.ofFn c) =
      decide (Odd (H.weightedPathCount w s t B))) := by
  let G := H.normalizedGraph w s t (le_inputMaxWeight w)
  let p := H.normalizedWeight w s t (le_inputMaxWeight w)
  let M := samplingBlockSize n (G.samplingDegree p)*(n+4)
  have hmax : inputMaxWeight w ≤ W := Finset.sup_le fun e _ => hw e
  have hm : ((n+m+inputMaxWeight w+1 : ℕ) : ℝ) ≤ ((n+m+W+1 : ℕ) : ℝ) := by
    exact_mod_cast (show n+m+inputMaxWeight w+1 ≤ n+m+W+1 by omega)
  have hbase : 0 ≤ 2-(1/2 : ℝ)^d := by
    linarith [pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) (n := d)]
  have ht : (G.parityCoinCount p s t M : ℝ) ≤
      17*(2-(1/2:ℝ)^d)^n*((n+m+inputMaxWeight w+1 : ℕ) : ℝ)^3 :=
    H.parity_coin_budget w s t (le_inputMaxWeight w) hd hdeg
  have hfactor := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hm 3)
    (by positivity : 0 ≤ 17*(2-(1/2:ℝ)^d)^n)
  have hlen : G.parityCoinCount p s t M ≤ L := Nat.cast_le.mp ((ht.trans hfactor).trans hL)
  have hp := H.streamed_weightedParity_probability w s t (le_inputMaxWeight w) hst B L hlen
  apply hp.trans (probability_mono ?_)
  intro c success
  let split := G.parityCoinBlocks p s t (G.orderedMaskIndex p s t) M
  change decide (G.streamedEstimate p s t (inputMaxWeight w) M (encInt B)
    (split (fun i => coinAt (List.ofFn c) i.val)).1 (split (fun i => coinAt (List.ofFn c) i.val)).2 ≠ 0) = _
  rw [coinAt_ofFn c hlen]
  exact success

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianInputEstimator

section HamiltonianPackedGraph

namespace DirectedHamiltonicity.Main.NativeGraph

open Multidigraph InputRAM Classical TargetedSamplers.Structured.BinaryStack TargetedSamplers.NumericFields

variable {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ) (hw : ∀ e, w e ≤ W) (s t : Fin n)

theorem adjacencyBits_bit (a v : Fin n) (k : Fin (W+1)) :
    bit (packed (adjacencyBits H w hw s t)) (gridOffset a v k)=decide (H.retainArc w s t hw (a,v,k)) :=
  (bit_testBit ..).trans (adjacencyBits_testBit H w hw s t a v k)

def arguments (n h s t graph mask key index mode : ℕ) : List ℕ := [n,h,s,t,graph,mask,key,index,mode]

theorem field_arguments (width n h s t g mask key index mode i : ℕ)
    (valid : ∀ x∈arguments n h s t g mask key index mode,x < 2^width) (hi : i < 9) :
    field i (pack width (arguments n h s t g mask key index mode))=
      (arguments n h s t g mask key index mode)[i]'(by simpa [arguments] using hi) :=
  field_pack width _ rfl valid i hi

theorem range_map_as_ofFn {α : Type*} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f=List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro j left right;simp [List.getElem_range]

/-- Decoding the numeric request reconstructs the typed normalized input, including
absent arcs and every zero coefficient. -/
theorem instance_arguments (width mask key index mode : ℕ)
    (enough : n ≤ width ∧ W+1 ≤ width)
    (valid : ∀ x∈arguments n (W+1) s.val t.val (packed (adjacencyBits H w hw s t)) mask key index mode, x < 2^width) :
    instanceOfRequest (pack width (arguments n (W+1) s.val t.val (packed (adjacencyBits H w hw s t)) mask key index mode)) =
      instanceData H w hw s t := by
  let g := packed (adjacencyBits H w hw s t)
  let xs := arguments n (W+1) s.val t.val g mask key index mode
  let z := pack width xs
  have rd (i : ℕ) (hi : i < 9) : field i z=xs[i]'(by change i < 9;exact hi) :=
    field_arguments width n (W+1) s.val t.val g mask key index mode i valid hi
  have h0 : field 0 z=n := rd 0 (by decide)
  have h1 : field 1 z=W+1 := rd 1 (by decide)
  have h2 : field 2 z=s.val := rd 2 (by decide)
  have h3 : field 3 z=t.val := rd 3 (by decide)
  have h4 : field 4 z=g := rd 4 (by decide)
  have bits : z.bits.length=width*9+1 := by
    rw [Nat.size_eq_bits_len];exact pack_size width xs valid
  have vs : requestLabels z 0=List.range n := by simp [requestLabels,slots,h0,bits,Nat.min_eq_left (by omega : n ≤ width*9+1)]
  have bs : requestLabels z 1=List.range (W+1) := by simp [requestLabels,slots,h1,bits,Nat.min_eq_left (by omega : W+1 ≤ width*9+1)]
  change (graphOfRequest z,(field 2 z,field 3 z))=(graphData H w hw s t,(s.val,t.val))
  rw [h2,h3]
  apply congrArg (fun A : Graph => (A,(s.val,t.val)))
  simp only [graphOfRequest,vs,bs,h0,h1,h4,range_map_as_ofFn,graphData]
  apply congrArg List.ofFn
  funext a
  apply congrArg List.ofFn
  funext v
  apply congrArg List.ofFn
  funext k
  exact adjacencyBits_bit H w hw s t a v k

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianPackedGraph

section HamiltonianArgumentBounds

namespace DirectedHamiltonicity.Main.InputRAM

open Multidigraph NativeGraph Classical TargetedSamplers.Structured.BinaryStack

variable {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ) (hw : ∀ e, w e ≤ W) (s t : Fin n)

theorem retained_card_bound : Fintype.card (H.RetainedArc w s t hw) ≤ n*(n*(W+1)) := by
  have h := Fintype.card_subtype_le (H.retainArc w s t hw)
  simpa [ArcType] using h

theorem random_field_widths :
    let G := H.normalizedGraph w s t hw
    let p := H.normalizedWeight w s t hw
    let mask := Fintype.card (G.MaskIndex p s t)
    let trial := Nat.clog 2 (Fintype.card (G.NonzeroCoeffs p s t))
    mask+1 ≤ argumentWidth n (W+1) ∧ trial+1 ≤ argumentWidth n (W+1) := by
  intro G p mask trial
  let e := Fintype.card (H.RetainedArc w s t hw)
  have h := retained_card_bound H w hw s t
  have hmul := Nat.mul_le_mul_left n (Nat.succ_le_succ h)
  have masks : mask ≤ n*e := by
    have bound := G.parityCoinCount_le p s t 0
    simpa only [parityCoinCount,Nat.zero_mul,Nat.add_zero,Fintype.card_fin] using bound
  have trialBits : trial ≤ n*(e+1) := by simpa only [Fintype.card_fin] using G.coefficient_block_width p s t
  have both := (argumentWidth_room n (W+1)).2.1
  change n*(e+1) ≤ n*(n*(n*(W+1))+1) at hmul
  have lift : n*e ≤ n*(e+1) := Nat.mul_le_mul_left n (Nat.le_succ e)
  omega

theorem word_fits_field {width : ℕ} (xs : List Bool) (bits : xs.length+1 ≤ width) :
    packed xs < 2^width := (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (by simpa using bits))

theorem internal_count (distinct : s ≠ t) : (internalLabels s t).card=n-2 := by
  have sets : internalLabels s t=(Finset.univ.erase s).erase t := by ext v;simp [internalLabels,and_comm]
  rw [sets,Finset.card_erase_of_mem (by simp [Ne.symm distinct]),Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ,Fintype.card_fin]
  omega

theorem reduced_count : (Finset.univ.filter (fun v : Fin n => v ≠ s)).card=n-1 := by
  have sets : (Finset.univ.filter (fun v : Fin n => v ≠ s))=Finset.univ.erase s := by ext v;simp
  rw [sets,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin]

theorem argument_index_bounds (q : ℕ) (positive : 0 < n) (small : q ≤ n) :
    q*(q+1) ≤ argumentWidth n (W+1) ∧ (n-1)*W ≤ argumentWidth n (W+1) := by
  let N := n*(n*(W+1))
  have hn : 1 ≤ n := positive
  have h₁ : n ≤ n*(W+1) := by simpa using Nat.mul_le_mul_left n (Nat.succ_le_succ (Nat.zero_le W))
  have h₂ : n*(W+1) ≤ N := by simpa [N] using Nat.mul_le_mul_right (n*(W+1)) hn
  have reach : q*(q+1) ≤ n*(N+1) := Nat.mul_le_mul small (Nat.succ_le_succ (small.trans (h₁.trans h₂)))
  have target : (n-1)*W ≤ n*(W+1) := Nat.mul_le_mul (Nat.sub_le n 1) (Nat.le_succ W)
  have first := (argumentWidth_room n (W+1)).2.1
  have second := (argumentWidth_room n (W+1)).1
  change n*(N+1)+1 ≤ _ at first
  change N+1 ≤ _ at second
  omega

/-- Each of the nine packed fields fits the common radix, even when the graph and random
arguments are exponentially valued. The scalar index is a row entry or target degree. -/
theorem all_arguments_fit (mask key index kind : ℕ) :
    let width := argumentWidth n (W+1)
    mask < 2^width → key < 2^width → index ≤ width → kind ≤ 3 →
      ∀ z∈arguments n (W+1) s.val t.val (packed (adjacencyBits H w hw s t)) mask key index kind, z < 2^width := by
  intro width hm hk hi mode
  have room := (argumentWidth_room n (W+1)).2.2
  have scal (v : ℕ) (h : v ≤ width) : v < 2^width := h.trans_lt width.lt_two_pow_self
  have sn := s.isLt
  have tn := t.isLt
  have g : packed (adjacencyBits H w hw s t) < 2^width := word_fits_field _ (by
    rw [adjacencyBits_length];exact (argumentWidth_room n (W+1)).1)
  intro z mem
  simp [arguments] at mem
  rcases mem with eq|eq|eq|eq|eq|eq|eq|eq|eq <;> rw [eq] <;>
    first | exact hm | exact hk | exact g | apply scal <;> change _ ≤ argumentWidth n (W+1) <;> omega

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianArgumentBounds

section HamiltonianGraphPort

namespace DirectedHamiltonicity.Main.InputRAM

open Multidigraph NativeGraph Classical TargetedSamplers TargetedSamplers.Structured

open TargetedSamplers.Structured.Word TargetedSamplers.Structured.BinaryStack

open TargetedSamplers.NumericFields OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem request_fields {bank n h source sink g width mask key index kind : ℕ} {u : Store}
    (o : RequestHeader (cell bank) n h source sink g width u) (a : RequestArgs (cell bank) mask key index kind u)
    (i : ℕ) (hi : i < 9) :
    u.mem (cell (bank+i))=(arguments n h source sink g mask key index kind)[i]'(by simpa [arguments] using hi) := by
  have off : cell (bank+i)=cell bank+i := by dsimp [cell];omega
  rw [off]
  interval_cases i <;> first
    | exact o.vertices | exact o.weights | exact o.src | exact o.dst | exact o.adjacency
    | exact a.maskWord | exact a.keyWord | exact a.indexWord | exact a.kindWord

/-- The same fixed machine handles mask length, tuple cardinality, each affine
entry and each determinant bit, for all graph sizes and all numeric keys. -/
theorem uniform_graph_query (det : List (List ℤ) → ℤ) (fast : Poly det) :
    ∃ (floor : ℕ) (command : ℕ → Cmd) (required work : Polynomial ℕ), ∀ {n m W : ℕ}
      (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ) (hw : ∀ e, w e ≤ W) (s t : Fin n)
      (bank width mask key index kind b : ℕ) (τ : Tapes) (u : Store),
      let graph := packed (adjacencyBits H w hw s t)
      let xs := arguments n (W+1) s.val t.val graph mask key index kind
      floor ≤ bank → n ≤ width ∧ W+1 ≤ width → (∀ z∈xs,z < 2^width) → required.eval width ≤ b →
      RequestHeader (cell bank) n (W+1) s.val t.val graph width u → RequestArgs (cell bank) mask key index kind u → u.Fits b →
      ∃ v j, Exec τ (fun y => y.Fits b) (command bank) u v j ∧ j ≤ work.eval b ∧
        v.mem 0=instanceAnswer det (instanceData H w hw s t) mask key index kind ∧ v.out=u.out ∧
        ∀ a ≥ cell floor,v.mem a=u.mem a := by
  obtain ⟨floor,kernel,req,work,call⟩ := StackMachine.fields_call (respond det) (respond_poly det fast) 9 (by decide)
  refine ⟨floor,kernel,req,work,?_⟩
  intro n m W H w hw s t bank width mask key index kind b τ u graph xs high fieldRoom valid space header args fu
  have rad : u.mem (cell (bank+9))=2^width := by simpa only [cell,Nat.add_assoc] using header.radix
  obtain ⟨v,j,exec,cost,val,out,keep⟩ := call bank width xs rfl valid τ u b high space fu rad (request_fields header args)
  let z := pack width xs
  have rd (i : ℕ) (hi : i < 9) : field i z=xs[i]'(by change i < 9;exact hi) := field_pack width xs rfl valid i hi
  have maskEq : field 5 z=mask := rd 5 (by decide)
  have keyEq : field 6 z=key := rd 6 (by decide)
  have indexEq : field 7 z=index := rd 7 (by decide)
  have kindEq : field 8 z=kind := rd 8 (by decide)
  change v.mem 0=instanceAnswer det (instanceOfRequest z) (field 5 z) (field 6 z) (field 7 z) (field 8 z) at val
  have inst : instanceOfRequest z=instanceData H w hw s t := instance_arguments H w hw s t width mask key index kind fieldRoom valid
  rw [inst,maskEq,keyEq,indexEq,kindEq] at val
  refine ⟨v,j,exec,cost,val,out,?_⟩
  intro a ha
  have ix : cell (a-14)=a := by dsimp [cell] at *;omega
  simpa only [ix] using keep (a-14) (by dsimp [cell] at ha;omega)

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianGraphPort

section HamiltonianRAMGraphTrials

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.BinaryStack

open Multidigraph FiniteSampling NativeGraph AffinePrefixEnumeration EditGV897.Main Classical

open IntegerDeterminantInterpolation.Native

open scoped BigOperators

variable {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ)

variable (hw : ∀ e, w e ≤ W) (s t : Fin n)

local notation "G₀" => H.normalizedGraph w s t hw

local notation "w₀" => H.normalizedWeight w s t hw

local notation "X₀" => instanceData H w hw s t

noncomputable def graphParameters (bank M B seenBase : ℕ) (coins : List Bool) : TrialParameters :=
  let length := Fintype.card ((G₀).MaskIndex w₀ s t)
  ⟨bank,n,W+1,s.val,t.val,packed (adjacencyBits H w hw s t),argumentWidth n (W+1),blockRank coins 0 length,length,
    Fintype.card ((G₀).NonzeroCoeffs w₀ s t),(internalLabels s t).card,M,B,seenBase⟩

noncomputable def trialSystems (M : ℕ) (coins : List Bool) (i : ℕ) : Option (List (Equation (internalLabels s t).card)) :=
  let z := (G₀).inputCoins w₀ s t M coins
  if hi : i < M then (G₀).trialEquations w₀ s t (internalOrder s t).symm ((G₀).coefficientRank w₀ s t) z.1 (z.2 ⟨i,hi⟩) else none

noncomputable def trialValue (M B : ℕ) (coins : List Bool) (x : List Bool) : ZMod 2 :=
  let z := (G₀).inputCoins w₀ s t M coins
  ((G₀).augLaplacian w₀ s t (subsetOfBits s t (internalOrder s t).symm x) z.1).det.coeff B

/-- The scalar inputs to the graph kernel, after setting its fixed-width request fields. -/
def GraphCall (det : List (List ℤ) → ℤ) (P : TrialParameters) (τ : Tapes) (b floor cost : ℕ) (kernel : Cmd) : Prop :=
  ∀ (mask key index mode : ℕ) (u : Store), mask < 2^P.fieldWidth → key < 2^P.fieldWidth → index ≤ P.fieldWidth → mode ≤ 3 →
    P.header u → RequestArgs P.a mask key index mode u → u.Fits b →
    ∃ y j, Exec τ (fun z => z.Fits b) kernel u y j ∧ j ≤ cost ∧ y.mem 0=instanceAnswer det X₀ mask key index mode ∧
      y.out=u.out ∧ ∀ x ≥ floor,y.mem x=u.mem x

private theorem get_word_at (ws : List ℕ) (j : ℕ) (h : j < ws.length) :
    ws[j]?.getD 0=ws[j] := by simp only [List.getElem?_eq_getElem h,Option.getD_some]

theorem graph_queries (bank M B seenBase b floor cost : ℕ) (τ : Tapes) (kernel : Cmd) (det : List (List ℤ) → ℤ)
    (correct : ∀ l (A : Matrix (Fin l) (Fin l) ℤ), det (matrixRows A)=A.det) (target : B ≤ (n-1)*W) :
    let P := graphParameters H w hw s t bank M B seenBase τ.coins
    GraphCall H w hw s t det P τ b floor cost kernel →
      P.Queries τ b floor cost kernel (trialSystems H w hw s t M τ.coins) (trialValue H w hw s t M B τ.coins) := by
  intro P call
  let G := G₀
  let p := w₀
  let z := G.inputCoins p s t M τ.coins
  let rank := G.coefficientRank p s t
  let sys := trialSystems H w hw s t M τ.coins
  have rk (i : ℕ) (hi : i < M) : (binaryRank _ (z.2 ⟨i,hi⟩)).val=P.key τ i :=
    G.inputCoins_rank p s t M τ.coins ⟨i,hi⟩
  have prod : G.coeffRadixProduct p s t=P.card := G.coeffRadixProduct_eq_card p s t
  have carry : CarriesMask G p s t P.mask z.1 := G.inputCoins_mask p s t M τ.coins
  have npos : 0 < n := by have := s.isLt;omega
  have dim : P.dim ≤ n := by change (internalLabels s t).card ≤ n;simpa using Finset.card_le_univ (internalLabels s t)
  have idx := argument_index_bounds (W := W) P.dim npos dim
  have widths := random_field_widths H w hw s t
  have maskRoom : P.mask < 2^P.fieldWidth := (binaryRank _ _).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (by change P.maskLength ≤ P.fieldWidth;exact (Nat.le_succ _).trans widths.1))
  have bitRoom (i : ℕ) : P.key τ i < 2^P.fieldWidth := (binaryRank _ _).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (by change Nat.clog 2 P.card ≤ P.fieldWidth;exact (Nat.le_succ _).trans widths.2))
  constructor
  · intro i hi miss
    have fail : ¬(binaryRank _ (z.2 ⟨i,hi⟩)).val < G.coeffRadixProduct p s t := by rw [rk i hi,prod];omega
    change (if h : i < M then G.trialEquations p s t _ rank z.1 (z.2 ⟨i,h⟩) else none)=none
    split
    · simp only [trialEquations,decodeRank,dif_neg fail,Option.map_none]
    · rfl
  · intro i hi hit
    have good : (binaryRank _ (z.2 ⟨i,hi⟩)).val < G.coeffRadixProduct p s t := by rwa [rk i hi,prod]
    let a := rank.symm ⟨(binaryRank _ (z.2 ⟨i,hi⟩)).val,good⟩
    let E := G.samplingSystem p s t (internalOrder s t).symm z.1 (fun j => (a j).val)
    have keyAt : (rank a).val=P.key τ i := (congrArg Fin.val (rank.apply_symm_apply _)).trans (rk i hi)
    have chosen : sys i=some E := by
      change (if h : i < M then G.trialEquations p s t _ rank z.1 (z.2 ⟨i,h⟩) else none)=some E
      split
      · simp only [trialEquations,decodeRank,dif_pos good,Option.map_some] <;> rfl
      · rename_i no; exact (no hi).elim
    have len : E.length=P.dim := by simp [E,samplingSystem] <;> rfl
    refine ⟨E,chosen,len,?_⟩
    intro j hj u header args fit
    have span := (TrialParameters.denseWords_shape E).trans (congrArg (·*(P.dim+1)) len)
    have jbound : j < P.dim*(P.dim+1) := hj.trans_le span.le
    obtain ⟨v,l,path,work,ans,out,frame⟩ := call P.mask (P.key τ i) j 2 u maskRoom (bitRoom i) (jbound.le.trans idx.1)
      (by decide) header args fit
    have val := affine_request H w hw s t det P.mask z.1 carry a ⟨j,jbound⟩
    change instanceAnswer det X₀ P.mask (rank a).val j 2=(denseWords E)[j]?.getD 0 at val
    rw [keyAt] at val
    exact ⟨v,l,path,work,ans.trans (val.trans (get_word_at (denseWords E) j hj)),out,frame⟩
  · intro xs len u header args fit
    have wroom : xs.length+1 ≤ P.fieldWidth := by
      have small := (argumentWidth_room n (W+1)).2.2
      change xs.length+1 ≤ argumentWidth n (W+1);omega
    obtain ⟨v,l,path,work,ans,out,frame⟩ := call P.mask (packed xs) B 3 u maskRoom (word_fits_field _ wroom)
      (target.trans idx.2) (by decide) header args fit
    have degree : B < (Finset.univ.filter (fun i : Fin n => i ≠ s)).card*W+1 := by rw [reduced_count s];omega
    have val := leaf_request H w hw s t det correct P.mask (packed xs) z.1 carry _ (carries_packed_subset s t xs len) ⟨B,degree⟩
    exact ⟨v,l,path,work,ans.trans val,out,frame⟩

theorem graph_estimate (bank M B seenBase : ℕ) (coins : List Bool) :
    let P := graphParameters H w hw s t bank M B seenBase coins
    let z := (G₀).inputCoins w₀ s t M coins
    P.estimate (trialSystems H w hw s t M coins) (trialValue H w hw s t M B coins)=
      decide ((G₀).parityEstimate w₀ s t (rankedCode ((G₀).coefficientRank w₀ s t)) M (B:ℤ) z ≠ 0) := by
  intro P z
  let rank := (G₀).coefficientRank w₀ s t
  let words := (G₀).trialAt w₀ s t (internalOrder s t).symm rank z.1 M z.2
  have eq (i : ℕ) : wordsByRank (trialSystems H w hw s t M coins i)=words i := by
    by_cases h : i < M <;> simp [words,trialSystems,trialAt,h,wordsByRank,z,rank]
  have law := (G₀).parity_as_capped_run w₀ s t (internalOrder s t).symm rank z.1 M B z.2
  let evaluate (xs : ℕ → List (List Bool)) :=
    if prefixReports (fun i => (xs i).length) M ≤ 12*M then
      TrialParameters.emits (trialValue H w hw s t M B coins)
        (applyPrefix (fun i => applyPrefix (insertAt (xs i)) (xs i).length) M ∅)
    else false
  have converted : P.estimate (trialSystems H w hw s t M coins) (trialValue H w hw s t M B coins)=evaluate words :=
    congrArg evaluate (funext eq)
  let reports := prefixReports (fun i => (words i).length) M
  let reported := applyPrefix (fun i => applyPrefix (insertAt (words i)) (words i).length) M ∅
  let totalCoeff : ZMod 2 := ∑ x ∈ reported, trialValue H w hw s t M B coins x
  have sample : (G₀).parityEstimate w₀ s t (rankedCode rank) M (B:ℤ) z=
      (if reports ≤ 12*M then totalCoeff else 0) := law
  rw [converted,sample]
  change (if reports ≤ 12*M then decide (totalCoeff ≠ 0) else false)=
    decide ((if reports ≤ 12*M then totalCoeff else 0) ≠ 0)
  by_cases guard : reports ≤ 12*M <;> simp [guard]

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMGraphTrials

section HamiltonianRAMAddressBounds

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.BinaryStack Multidigraph

theorem trial_count_bits (n d : ℕ) :
    (samplingBlockSize n d*(n+4)).size ≤ scheduleWidth n d := by
  let A := trialNumerator n d
  let D := trialDenominator n d
  let x := A+D-1
  have bound := (schedule_word_sizes n d).2.2
  change (2*x+2).size ≤ (d+1)*(n-2)+3 at bound
  have div := Nat.div_le_self x D
  have estimate : (2*(x/D)).size ≤ (d+1)*(n-2)+3 := (Nat.size_le_size (show 2*(x/D) ≤ 2*x+2 by omega)).trans bound
  rw [← integerBlockSize_eq]
  change (2*(x/D)*(n+4)).size ≤ scheduleWidth n d
  have h := size_mul_le_add (2*(x/D)) (n+4)
  have small : (n+4).size ≤ n+4 := Nat.size_le.mpr (n+4).lt_two_pow_self
  unfold scheduleWidth;omega

theorem cap_bits (M : ℕ) : (12*M).size ≤ M.size+4 := by
  have p := size_mul_le_add 12 M
  rw [show (12:ℕ).size=4 by decide] at p
  omega

/-- Random-access block addresses use the bit length of the trial counter.
The numerical value of an exponential trial index never enters the running-time polynomial. -/
theorem trial_address_bits {mask k i M w : ℕ} (mi : mask ≤ w) (ki : k ≤ w) (idx : i ≤ M) :
    (mask+k*i+k+2*k+2).size ≤ M.size+w+6 := by
  let L := M.size+w+2
  have kb : k.size ≤ w := (Nat.size_le.mpr k.lt_two_pow_self).trans ki
  have mb : mask.size ≤ w := (Nat.size_le.mpr mask.lt_two_pow_self).trans mi
  have ib := Nat.size_le_size idx
  have prod := size_mul_le_add k i
  have twice := size_mul_le_add 2 k
  have bit : (2:ℕ).size=2 := by decide
  rw [bit] at twice
  have w : w ≤ L := by dsimp [L];omega
  have p : (k*i).size ≤ L := by dsimp [L];omega
  have s₁ := size_add_le_succ (mb.trans w) p
  have s₂ := size_add_le_succ s₁ (by omega : k.size ≤ L+1)
  have s₃ := size_add_le_succ s₂ (by dsimp [L];omega : (2*k).size ≤ L+1+1)
  have s₄ := size_add_le_succ s₃ (by rw [bit];omega : (2:ℕ).size ≤ L+1+1+1)
  dsimp [L] at s₄;omega

theorem visited_address_bits {q : ℕ} (base : ℕ) (xs : List Bool) (width : xs.length=q) :
    (base+packed xs).size ≤ base+q+2 := by
  have addr : base.size ≤ base := Nat.size_le.mpr base.lt_two_pow_self
  have key : (packed xs).size=q+1 := by simp [width]
  exact (size_add_le_succ (by omega : base.size ≤ base+q+1) (by omega : (packed xs).size ≤ base+q+1))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMAddressBounds

section HamiltonianRAMCapacity

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.BinaryStack AffinePrefixEnumeration Multidigraph

open Polynomial

private theorem eval_monotone (p : Polynomial ℕ) : Monotone (fun x => p.eval x) := by
  induction p using Polynomial.induction_on' with
  | monomial d c => intro x y h;simp only [Polynomial.eval_monomial];exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h d)
  | add p q hp hq => intro x y h;simp only [Polynomial.eval_add];exact Nat.add_le_add (hp h) (hq h)

/-- A polynomial upper bound on the numerical addresses of the row array, solver buffer,
and sparse table base. The sparse key itself is charged by bit length. -/
def heapBound (bank c d x : ℕ) := cell bank+104+x*(x+1)+x+c*(3*x+1)^d+(132+3*x+x^3)+2

noncomputable def capacity (required : Polynomial ℕ) (bank c d solverFloor : ℕ) : Polynomial ℕ :=
  let x : Polynomial ℕ := Polynomial.X+2
  let addr := Polynomial.C (cell bank+104)+x*(x+1)+x+Polynomial.C c*(3*x+1)^d+(132+3*x+x^3)+2
  required.comp (24*x^4)+4*(addr+(3*x+1)^d+Polynomial.C c+Polynomial.C d+3*x+20)+
    1024*x^4+Polynomial.C solverFloor

theorem capacity_eval (required : Polynomial ℕ) (bank c d floor S : ℕ) :
    let x := S+2
    (capacity required bank c d floor).eval S = required.eval (24*x^4)+
      4*(heapBound bank c d x+(3*x+1)^d+c+d+3*x+20)+1024*x^4+floor := by
  intro x
  simp only [capacity,heapBound,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_C,
    Polynomial.eval_one,Polynomial.eval_ofNat,Polynomial.eval_comp,Polynomial.eval_X,x]

structure InputRoom (P : TrialParameters) (S : Solver) (required : Polynomial ℕ) (floor b n m W V c d : ℕ) : Prop where
  parser : 256*(n+m+W+3)^2 ≤ b
  grid : (128+3*m+2+2*(n*(n*(V+1)))+2*n+2).size ≤ b
  width : argumentWidth n (V+1)+2 ≤ b
  cap : (12*P.trials).size ≤ b
  setup : solverRoom P.bank P.dim c d (128+3*m+2+n*(n*(V+1))) ≤ b
  native : required.eval P.fieldWidth ≤ b
  loopSpace : P.Space S floor b
  gridSize : n*(n*(V+1)) ≤ b
  edges : m ≤ b
  exp : d ≤ b
  dim : P.dim ≤ b
  fields : P.fieldWidth ≤ b
  masks : P.maskLength+1 ≤ b
  solverWork : S.work P.N ≤ b

theorem capacity_enough (P : TrialParameters) (S : Solver) (required : Polynomial ℕ)
    (n m W V degree c d floor b : ℕ) (weights : V ≤ W) (deg : degree ≤ V+1) (q : P.dim ≤ n)
    (width : P.fieldWidth=argumentWidth n (V+1)) (mask : P.maskLength+1 ≤ P.fieldWidth)
    (coins : Nat.clog 2 P.card+1 ≤ P.fieldWidth) (trials : P.trials=samplingBlockSize n degree*(n+4))
    (base : P.seenBase=seenArea P.bank P.dim c d (128+3*m+2+n*(n*(V+1))))
    (grow : ∀ N, S.work N+S.space N ≤ c*(N+1)^d) (nativeFloor : floor ≤ P.a) (solverFloor : S.floor ≤ P.a)
    (room : (capacity required P.bank c d S.floor).eval (n+m+W+1) ≤ b) :
    InputRoom P S required floor b n m W V c d := by
  let x := n+m+W+3
  let U := 24*x^4
  let A := heapBound P.bank c d x
  let F := (3*x+1)^d
  have cap := capacity_eval required P.bank c d S.floor (n+m+W+1)
  change (capacity required P.bank c d S.floor).eval (n+m+W+1)=required.eval U+4*(A+F+c+d+3*x+20)+1024*x^4+S.floor at cap
  rw [cap] at room
  have pos : 1 ≤ x := by dsimp [x];omega
  have nx : n ≤ x := by dsimp [x];omega
  have mx : m ≤ x := by dsimp [x];omega
  have vx : V+1 ≤ x := by dsimp [x];omega
  have dx : n+degree+2 ≤ x := by dsimp [x];omega
  have qx : P.dim ≤ x := q.trans nx
  have ns : n*(n*(V+1)) ≤ x^3 := by
    simpa only [pow_succ,pow_zero,one_mul,Nat.mul_assoc] using (Nat.mul_le_mul nx (Nat.mul_le_mul nx vx))
  have up (i : ℕ) (h : i ≤ 4) : x^i ≤ x^4 := Nat.pow_le_pow_right pos h
  have x4 : x ≤ x^4 := by simpa using up 1 (by decide)
  have cubic := up 3 (by decide)
  have sq := up 2 (by decide)
  have fw : P.fieldWidth ≤ U := by
    rw [width];exact (argumentWidth_le n m V).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [x];omega) _))
  have timeBits : P.trials.size ≤ 18*x^2 := by
    rw [trials]
    exact (trial_count_bits n degree).trans ((schedule_polynomial n degree).1.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left dx 2)))
  have power : (P.N+1)^d ≤ F := Nat.pow_le_pow_left (by dsimp [TrialParameters.N];omega) d
  have scaled := Nat.mul_le_mul_left c power
  have sp := grow P.N
  have row : P.row=P.a+104 := rfl
  have pin : P.pin=P.row+P.dim*(P.dim+1) := rfl
  have dest : P.base=P.pin+P.dim := rfl
  have qq : P.dim*(P.dim+1) ≤ x*(x+1) := Nat.mul_le_mul qx (Nat.succ_le_succ qx)
  have seen : P.seenBase ≤ A := by
    rw [base];dsimp [seenArea,solverArea,pinArea,rowArea,A,heapBound]
    change c*(P.dim+(P.dim+P.dim)+1)^d ≤ c*(3*x+1)^d at scaled
    omega
  have seenHere : P.seenBase=P.base+c*(P.N+1)^d+(128+3*m+2+n*(n*(V+1)))+2 := base
  have aa : c*F ≤ A := by dsimp [A,heapBound,F];omega
  have actual : solverRoom P.bank P.dim c d (128+3*m+2+n*(n*(V+1))) ≤ 4*(A+F+c+d+3*x+20) := by
    unfold solverRoom
    rw [← base]
    exact Nat.mul_le_mul_left 4 (by change (P.dim+(P.dim+P.dim)+1)^d ≤ F at power;omega)
  have roomW : U+18*x^2+x+10 ≤ 1024*x^4 := by dsimp [U];nlinarith only [x4,sq,pos]
  have whole : ∀ v : ℕ, v ≤ P.seenBase+P.dim+2 → v ≤ b := by intro z hz;omega
  have bytes (v : ℕ) : v.size ≤ v := Nat.size_le.mpr v.lt_two_pow_self
  have roomFor : P.Space S floor b := {
    two := by omega
    floorQuery := nativeFloor
    floorSolve := solverFloor
    trialWidth := by omega
    seekWidth := by
      intro i hi
      exact (trial_address_bits (w := P.fieldWidth) (by omega) (by omega) hi.le).trans (by omega)
    rowWidth := (bytes _).trans (by omega)
    kernelWidth := by omega
    solverWidth := (bytes _).trans (by omega)
    floorWidth := (bytes _).trans (by omega)
    table := by omega
    seenWidth := fun xs hx => (visited_address_bits P.seenBase xs hx).trans (whole _ le_rfl)
    countWidth := by omega }
  have nativeCost : required.eval P.fieldWidth ≤ required.eval U := eval_monotone required fw
  have nativeRoom : required.eval U ≤ b := by omega
  refine ⟨by change 256*x^2 ≤ b;omega,(bytes _).trans (by omega),by rw [← width];omega,
    (cap_bits P.trials).trans (by omega),by omega,nativeCost.trans nativeRoom,roomFor,
    by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMCapacity

section HamiltonianRAMCost

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers.Structured AffinePrefixEnumeration Polynomial

noncomputable def bodyWork (kernel : Polynomial ℕ) : Polynomial ℕ :=
  let x : Polynomial ℕ := X
  let op := x*(5*x+9)+15
  let prep := 6*op+x*(5*op+18*x+19)+14*x+16+(x+30)*op
  let init := (x+30)*op+2*kernel+4*x+9*x+10
  let count := 4*op+9*x+x*(x+1)*(kernel+5)+x+12
  let visit := x*(x+10)+kernel+17
  prep+init+((count+4)+(count+5)+12*(visit+3))+5

theorem body_work_bound (P : TrialParameters) (S : Solver) (kernel : Polynomial ℕ) (b m grid wbits d c : ℕ)
    (gridBound : grid ≤ b) (edges : m ≤ b) (fields : wbits ≤ b) (degree : d ≤ b) (dim : P.dim ≤ b)
    (mask : P.maskLength ≤ b) (bits : Nat.clog 2 P.card ≤ b) (gauss : S.work P.N ≤ b) :
    let cost := kernel.eval b
    let L := b*(5*b+9)+15
    let count := P.countCost S b cost
    let visit := P.visitCost S cost
    ∀ j k l : ℕ,
      j ≤ 6*L+grid*(5*L+18*m+19)+14*grid+16+(wbits+initFields.length)*L →
      k ≤ (d+(initSolverLayout P.bank c d).length)*L+2*cost+4*Nat.clog 2 P.card+9*P.maskLength+10 →
      l ≤ P.trials*((count+4)+(count+5)+12*(visit+3))+5 →
      j+(k+l) ≤ (P.trials+1)*(bodyWork kernel).eval b := by
  intro cost L count visit j k l h₁ h₂ h₃
  let pre := 6*L+b*(5*L+18*b+19)+14*b+16+(b+30)*L
  let init := (b+30)*L+2*cost+4*b+9*b+10
  let c₀ := 4*L+9*b+b*(b+1)*(cost+5)+b+12
  let v₀ := b*(b+10)+cost+17
  let outer := (c₀+4)+(c₀+5)+12*(v₀+3)
  have len₁ : initFields.length ≤ 30 := by decide
  have len₂ : (initSolverLayout P.bank c d).length ≤ 30 := (show (initSolverLayout P.bank c d).length=21 from rfl).le.trans (by decide)
  have preB : j ≤ pre := h₁.trans (by dsimp [pre];gcongr)
  have initB : k ≤ init := h₂.trans (by dsimp [init];gcongr)
  have cnt : count ≤ c₀ := by dsimp [count,c₀,TrialParameters.countCost,L];gcongr
  have vis : visit ≤ v₀ := by dsimp [visit,v₀,TrialParameters.visitCost];gcongr
  have endB : l ≤ P.trials*outer+5 := h₃.trans (by dsimp [outer];gcongr)
  have full : (bodyWork kernel).eval b=pre+init+outer+5 := by
    simp only [bodyWork,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one,
      pre,init,outer,c₀,v₀,L,cost]
  rw [full,Nat.add_mul,Nat.one_mul]
  have lift := Nat.mul_le_mul_left P.trials (show outer ≤ pre+init+outer+5 by omega)
  omega

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMCost

section HamiltonianInputRunReduction

namespace DirectedHamiltonicity.Main

open Multidigraph Classical FiniteSampling

/-- Absorb all polynomial factors into one pair of public constants. The quantified
degree bound occurs only in the analysis; the program never receives it. -/
theorem proposition4_from_input_runs (P : TargetedSamplers.Program) (A k : ℕ) (run : BoundedInputRuns P A k) :
    ∃ (P : TargetedSamplers.Program) (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (d : ℕ), 1 ≤ d → ∀ (n m W : ℕ) (tail head : Fin m → Fin n) (w : Fin m → ℕ),
        (∀ e, w e ≤ W) →
        (∀ v, (Multidigraph.incomingWeights
          (⟨tail, head⟩ : Multidigraph (Fin n) (Fin m)) w v).card ≤ d) →
        ∀ (s t : Fin n), s ≠ t → ∀ B : ℤ,
          (∀ coins : List Bool, ∃ (cost : ℕ) (b : Bool),
            P.RunsIn (runTapes (encodeParityInstance n m tail head w s t B) coins) cost (some [b]) ∧
            (cost : ℝ) ≤ C * (2 - (1 / 2 : ℝ) ^ d) ^ n * ((n + m + W + 1 : ℕ) : ℝ) ^ k) ∧
          (∀ L : ℕ, C * (2 - (1 / 2 : ℝ) ^ d) ^ n * ((n + m + W + 1 : ℕ) : ℝ) ^ k ≤ L →
            (5 / 6 : ℝ) ≤ outputProb P (encodeParityInstance n m tail head w s t B) L
              [decide (Odd (Multidigraph.weightedPathCount
                  (⟨tail, head⟩ : Multidigraph (Fin n) (Fin m)) w s t B))]) := by
  let C : ℝ := 17*((A:ℝ)+1)
  refine ⟨P,C,k+3,by dsimp [C];positivity,?_⟩
  intro d hd n m W tail head w hw deg s t distinct B
  let H : Multidigraph (Fin n) (Fin m) := ⟨tail,head⟩
  let small := le_inputMaxWeight w
  let G := H.normalizedGraph w s t small
  let p := H.normalizedWeight w s t small
  let M := samplingBlockSize n (G.samplingDegree p)*(n+4)
  let S : ℝ := (n+m+W+1 : ℕ)
  let base := (2-(1/2:ℝ)^d)^n
  have hs : 1 ≤ S := by dsimp [S];exact_mod_cast (show 1 ≤ n+m+W+1 by omega)
  have hb : 1 ≤ base := by
    apply one_le_pow₀
    linarith [pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) (n := d)]
  have trials : (M:ℝ) ≤ 4*((n:ℝ)+4)*base := by
    have eq := G.parity_trials_le p d hd (fun v => (Finset.card_le_card
      (H.normalizedGraph_incomingWeights w s t small v)).trans (deg v))
    simpa only [M,base,Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat] using eq
  have cap : (M:ℝ)+1 ≤ 17*base*S := by
    have ns : (n:ℝ)+4 ≤ 4*S := by dsimp [S];push_cast;linarith
    have g := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ns (by norm_num : (0:ℝ) ≤ 4)) (by linarith : 0 ≤ base)
    have extra : 1 ≤ base*S := one_le_mul_of_one_le_of_one_le hb hs
    nlinarith only [g,trials,extra]
  have coef : 17 ≤ C := by dsimp [C];linarith [Nat.cast_nonneg (α := ℝ) A]
  constructor
  · intro coins
    obtain ⟨cost,exec,work⟩ := run n m W tail head w hw s t distinct B coins
    refine ⟨cost,H.inputEstimator w s t (encInt B) coins,exec,?_⟩
    have wR : (cost:ℝ) ≤ ((M:ℝ)+1)*(A:ℝ)*S^k := by
      change cost ≤ (M+1)*A*(n+m+W+1)^k at work
      have h : (cost:ℝ) ≤ (((M+1)*A*(n+m+W+1)^k : ℕ):ℝ) := Nat.cast_le.mpr work
      simpa only [S,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using h
    have poly : S^(k+1) ≤ S^(k+3) := pow_le_pow_right₀ hs (by omega)
    calc
      _ ≤ ((M:ℝ)+1)*(A:ℝ)*S^k := wR
      _ ≤ (17*base*S)*(A:ℝ)*S^k := by gcongr
      _ = (17*(A:ℝ))*base*S^(k+1) := by rw [pow_succ];ring
      _ ≤ C*base*S^(k+3) := by
        have cA : 17*(A:ℝ) ≤ C := by dsimp [C];linarith
        exact mul_le_mul (mul_le_mul_of_nonneg_right cA (by linarith)) poly (by positivity)
          (mul_nonneg (by dsimp [C];positivity) (by linarith))
  · intro L length
    have budget : 17*base*S^3 ≤ C*base*S^(k+3) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right coef (by linarith)) (pow_le_pow_right₀ hs (by omega))
        (by positivity) (mul_nonneg (by linarith) (by linarith))
    have success := H.inputEstimator_success w s t hd hw deg distinct B (budget.trans length)
    exact success.trans (outputProb_ge_estimator P _ L _ _ (fun c => by
      obtain ⟨_,⟨z,halt,_,result⟩,_⟩ := run n m W tail head w hw s t distinct B (List.ofFn c)
      exact ⟨z,halt,result⟩))

end DirectedHamiltonicity.Main

end HamiltonianInputRunReduction

section HamiltonianRAMRealization

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.BinaryStack AffinePrefixEnumeration Multidigraph FiniteSampling NativeGraph Classical

open IntegerDeterminantInterpolation.Native OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem graph_body_exists (det : List (List ℤ) → ℤ) (fast : Poly det)
    (correct : ∀ l (A : Matrix (Fin l) (Fin l) ℤ), det (matrixRows A)=A.det) :
    ∃ (body : Cmd) (required work : Polynomial ℕ), ValidBodyRuns body required work := by
  obtain ⟨S⟩ := solver_exists
  obtain ⟨c,d,growth⟩ := S.growth
  obtain ⟨nativeFloor,commands,req,work,native⟩ := uniform_graph_query det fast
  let bank := max 128 (max nativeFloor S.floor)
  let cmd := commands bank
  have reserve : nativeFloor ≤ bank := by dsimp [bank];omega
  have low : 60 ≤ cell bank := by dsimp [bank,cell];omega
  have sep : cell nativeFloor ≤ cell bank := by dsimp [cell];omega
  have solverLow : S.floor ≤ cell bank := by dsimp [cell,bank];omega
  refine ⟨estimatorBody bank c d cmd S.command,capacity req bank c d S.floor,bodyWork work,?_⟩
  intro n m W tail head w hw s t distinct B coins H V G p degree M τ good u b enough fit view degAt target trials out fresh
  let cover := le_inputMaxWeight w
  let q := (internalLabels s t).card
  let N := n*(n*(V+1))
  let gridEnd := 128+3*m+2+N
  let seen := seenArea bank q c d gridEnd
  let P := graphParameters H w cover s t bank M B.toNat seen τ.coins
  let eqs := trialSystems H w cover s t M τ.coins
  let value := trialValue H w cover s t M B.toNat τ.coins
  have vmax : V ≤ W := Finset.sup_le fun e _ => hw e
  have degreeBound : degree ≤ V+1 := by
    apply samplingDegree_le G p (by omega)
    intro v
    have subset : G.incomingWeights p v⊆Finset.range (V+1) := by
      intro i hi
      obtain ⟨a,_,eq⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (eq ▸ a.1.2.2.isLt)
    simpa using Finset.card_le_card subset
  have dim : P.dim=n-2 := internal_count s t distinct
  have widths := random_field_widths H w cover s t
  have space := capacity_enough P S req n m W V degree c d (cell nativeFloor) b vmax degreeBound
    (dim.trans_le (Nat.sub_le ..)) rfl widths.1 widths.2 rfl rfl growth sep solverLow enough
  have num : GraphCall H w cover s t det P τ b (cell nativeFloor) (work.eval b) cmd := by
    intro mask key index kind v hm hk hi keyMode hd ha fv
    have scale := (argumentWidth_room n (V+1)).2.2
    exact native H w cover s t bank P.fieldWidth mask key index kind b τ v reserve
      (by change n ≤ argumentWidth n (V+1) ∧ V+1 ≤ argumentWidth n (V+1);omega)
      (all_arguments_fit H w cover s t mask key index kind hm hk hi keyMode) space.native hd ha fv
  have scalar (mode : Fin 2) (y : Store) (header : P.header y) (args : RequestArgs P.a 0 0 0 mode.val y) (fy : y.Fits b) :
      ∃ t k, Exec τ (fun z => z.Fits b) cmd y t k ∧ k ≤ work.eval b ∧
        t.mem 0=(if mode.val=0 then P.maskLength else P.card) ∧ t.out=y.out ∧ ∀ x ≥ cell nativeFloor,t.mem x=y.mem x := by
    obtain ⟨z,k,eval,wk,answer,ret,frame⟩ := num 0 0 0 mode.val y (by positivity) (by positivity) (Nat.zero_le _) (by omega) header args fy
    refine ⟨z,k,eval,wk,answer.trans ?_,ret,frame⟩
    fin_cases mode
    · exact mask_request H w cover s t det 0 0 0
    · exact cardinality_request H w cover s t det 0 0 0
  have nonneg := Int.toNat_of_nonneg good.1
  have degreeOK : B.toNat ≤ (n-1)*V := by exact_mod_cast (nonneg ▸ good.2 : ((B.toNat:ℕ):ℤ) ≤ (((n-1)*V:ℕ):ℤ))
  have calls := graph_queries H w cover s t bank M B.toNat seen b (cell nativeFloor) (work.eval b) τ cmd det correct degreeOK num
  obtain ⟨y,j,prepare,w₁,cached,outY,frame⟩ := prepareRequest_exec (τ := τ) cover bank M B.toNat u view trials target
    low fit space.loopSpace.two space.grid space.width space.cap
  have untouched (x : ℕ) (hx : P.a+68 < x) (above : gridEnd ≤ x) : y.mem x=0 := by
    apply (frame x hx above).trans
    apply fresh;dsimp [gridEnd,N,graphBase] at *;omega
  have maskEq : P.mask=(binaryRank P.maskLength fun i => τ.coins[i.val]?.getD false).val := by
    apply congrArg (fun g => (binaryRank P.maskLength g).val)
    funext i
    change τ.coins[0+i.val]?.getD false=τ.coins[i.val]?.getD false
    rw [Nat.zero_add]
  obtain ⟨v,k,init,w₂,initial,cur,total,outV⟩ := P.bootstrap_exec (τ := τ) c d gridEnd cmd value y cached rfl
    dim rfl maskEq untouched sep space.setup space.loopSpace.two space.masks
    space.loopSpace.trialWidth (prepare.post fit) scalar
  obtain ⟨z,l,run,w₃,outZ⟩ := P.runTrials_exec S cmd eqs value space.loopSpace calls v initial cur total (init.post (prepare.post fit))
  have budget := body_work_bound P S work b m N P.fieldWidth d c space.gridSize space.edges space.fields space.exp
    space.dim (Nat.le_of_succ_le space.masks) (Nat.le_of_succ_le space.loopSpace.trialWidth) space.solverWork
    j k l w₁ w₂ w₃
  have decoded := graph_estimate H w cover s t bank M B.toNat seen τ.coins
  let zeta := G.inputCoins p s t M τ.coins
  have targetEq : G.streamedEstimate p s t V M (encInt B) zeta.1 zeta.2=
      G.parityEstimate p s t (rankedCode (G.coefficientRank p s t)) M B zeta := by
    simpa only [List.append_nil,Prod.mk.eta] using
      G.streamedEstimate_eq p s t (fun e => Nat.le_of_lt_succ e.1.2.2.isLt) M B [] zeta.1 zeta.2
  have answer : P.estimate eqs value=H.inputEstimator w s t (encInt B) coins := by
    rw [decoded,nonneg]
    change decide (G.parityEstimate p s t _ M B zeta ≠ 0)=decide (G.streamedEstimate p s t V M (encInt B) zeta.1 zeta.2 ≠ 0)
    rw [targetEq]
  exact ⟨z,_,prepare.seq (init.seq run),budget,by rw [outZ,outV,outY,out,answer];rfl⟩

theorem bounded_input_runs_of_integer_det (h : ∃ det : List (List ℤ) → ℤ, Poly det ∧
    ∀ l (A : Matrix (Fin l) (Fin l) ℤ), det (matrixRows A)=A.det) :
    ∃ (P : Program) (A k : ℕ), BoundedInputRuns P A k := by
  obtain ⟨det,fast,correct⟩ := h
  obtain ⟨body,required,work,run⟩ := graph_body_exists det fast correct
  obtain ⟨A,k,full⟩ := bounded_of_valid_body body required work run
  exact ⟨_,A,k,full⟩

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMRealization

section Sol_DirectedHamiltonicity_Proposition4

open DirectedHamiltonicity.Main

theorem solution :
    ∃ (P : TargetedSamplers.Program) (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (d : ℕ), 1 ≤ d → ∀ (n m W : ℕ) (tail head : Fin m → Fin n) (w : Fin m → ℕ),
        (∀ e, w e ≤ W) →
        (∀ v, (Multidigraph.incomingWeights
          (⟨tail, head⟩ : Multidigraph (Fin n) (Fin m)) w v).card ≤ d) →
        ∀ (s t : Fin n), s ≠ t → ∀ B : ℤ,
          (∀ coins : List Bool, ∃ (cost : ℕ) (b : Bool),
            P.RunsIn (runTapes (encodeParityInstance n m tail head w s t B) coins) cost (some [b]) ∧
            (cost : ℝ) ≤ C * (2 - (1 / 2 : ℝ) ^ d) ^ n * ((n + m + W + 1 : ℕ) : ℝ) ^ k) ∧
          (∀ L : ℕ, C * (2 - (1 / 2 : ℝ) ^ d) ^ n * ((n + m + W + 1 : ℕ) : ℝ) ^ k ≤ L →
            (5 / 6 : ℝ) ≤ outputProb P (encodeParityInstance n m tail head w s t B) L
              [decide (Odd (Multidigraph.weightedPathCount
                (⟨tail, head⟩ : Multidigraph (Fin n) (Fin m)) w s t B))]) := by
  obtain ⟨P,A,k,run⟩ := InputRAM.bounded_input_runs_of_integer_det
    InfoLossLAR.WorstCase.RegevSketch.native_integer_determinant
  exact proposition4_from_input_runs P A k run

end Sol_DirectedHamiltonicity_Proposition4
