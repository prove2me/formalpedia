-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Ctx.completeSeq_validSeq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:57:20.219129+00:00
-- url     : https://prove2.me/submissions/5c251faf-696f-431d-8fd2-08d99029e2c7

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Bridge
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete
import all Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete
public import Theorems.Thm_BCFGJPSSV26_Greedy_testT_iff

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

namespace Ctx

variable (C : Ctx)

variable {C} {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)
include hX

/-- The tests of the algorithm after atoms in range are openability with `η = 0`. -/
theorem testT_iff_openT (b : Bool) (f : ℚ) {θ : ℚ} (hθ : 0 < θ) {S : List AAtom}
    (hS : ∀ a ∈ S, C.AtomOK a) {i : ℕ} (hi : i < C.ip.m) :
    C.testT b f θ (C.prof S) i = true ↔
      OpenT C.par X.d b f 0 θ (profL C.par.K X.d (decS hX S)) ⟨i, hi⟩ := by
  have h : C.testT b f θ (C.prof S) i =
      Greedy.testT C.par X.d b f θ (profL C.par.K X.d (decS hX S)) ⟨i, hi⟩ :=
    testT_eq hX b f θ (prof_getD hX hS) (prof_length _) ⟨i, hi⟩
  rw [h]
  exact testT_iff hX.good (fun j i ↦ X.d_nonneg j i) b hθ

section Iter

variable {b : Bool} {f θ : ℚ} {pre cur : List AAtom}

end Iter

/-- The atoms added by CompleteSequence are valid. -/
theorem seqStep_iter_valid {f η : ℚ} (hη : 0 ≤ η) {p : ℕ} {pre cur : List AAtom}
    (hok : ∀ a ∈ pre ++ cur, C.AtomOK a)
    (hcur : ∀ t (ht : t < cur.length), ValidAt C.par X.d f η p (decS hX (pre ++ cur.take t))
      (decA hX cur[t])) (k : ℕ) :
    ∀ t (ht : t < ((C.seqStep (typ1 p) f (C.θseq p) pre)^[k] cur).length),
      ValidAt C.par X.d f η p
        (decS hX (pre ++ ((C.seqStep (typ1 p) f (C.θseq p) pre)^[k] cur).take t))
        (decA hX ((C.seqStep (typ1 p) f (C.θseq p) pre)^[k] cur)[t]) := by
  induction k with
  | zero => exact hcur
  | succ k ih =>
    have hokW := C.seqStep_iter_ok (b := typ1 p) (f := f) (θ := C.θseq p) hok k
    rw [Function.iterate_succ_apply']
    revert ih hokW
    generalize (C.seqStep (typ1 p) f (C.θseq p) pre)^[k] cur = W
    intro ih hokW
    rcases C.seqStep_cases (typ1 p) f (C.θseq p) pre W with ⟨-, h⟩ | ⟨i, -, hi, ht, h⟩
    · rw [h]
      exact ih
    · rw [h]
      intro t ht'
      rw [List.length_append, List.length_singleton] at ht'
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with ht' | rfl
      · rw [List.take_append_of_le_length ht'.le, List.getElem_append_left ht']
        exact ih t ht'
      · rw [List.take_left, List.getElem_concat_length rfl]
        have hK := hX.K_pos
        refine ValidAt.of_open (fun a ha ↦ ?_) hη ?_
        · obtain ⟨a', -, rfl⟩ := List.mem_map.1 ha
          exact aoff_nonneg hK.le a'
        · rw [decA_fac hX hi]
          exact (testT_iff_openT hX (typ1 p) f (lt_of_lt_of_le one_pos (C.par.one_le_θ _))
            hokW hi).1 ht

/-- **CompleteSequence produces a valid sequence** ([BCFGJPSSV26a, Observation D.8]): if the
atoms of `cur` are valid after `pre`, the completion of `cur` is a valid sequence after `pre`. -/
theorem completeSeq_validSeq {f η : ℚ} (hf : C.ip.n * C.ip.η < f) (hη : 0 ≤ η) {p : ℕ}
    {pre cur : List AAtom} (hok : ∀ a ∈ pre ++ cur, C.AtomOK a)
    (hcur : ∀ t (ht : t < cur.length), ValidAt C.par X.d f η p (decS hX (pre ++ cur.take t))
      (decA hX cur[t])) :
    ValidSeq C.par X.d f η p (decS hX pre)
      (decS hX (C.completeSeq (typ1 p) f (C.θseq p) pre cur)) := by
  have hval := seqStep_iter_valid hX hη hok hcur C.ip.L
  have hnone := firstOpen_completeSeq hX (b := typ1 p) (θ := C.θseq p) (hX.f_pos hf) hok
  have hokH := C.completeSeq_ok (b := typ1 p) (f := f) (θ := C.θseq p) hok
  revert hval hnone hokH
  unfold completeSeq
  generalize (C.seqStep (typ1 p) f (C.θseq p) pre)^[C.ip.L] cur = H
  intro hval hnone hokH
  refine ⟨fun t ht ↦ ?_, fun i ho ↦ ?_⟩
  · have ht' : t < H.length := by simpa [decS] using ht
    have := hval t ht'
    simpa [decS, List.map_take] using this
  · have hfalse := List.find?_eq_none.1 hnone i (List.mem_range.2 i.isLt)
    rw [← decS_append] at ho
    exact hfalse ((testT_iff_openT hX (typ1 p) f
      (lt_of_lt_of_le one_pos (C.par.one_le_θ _)) hokH i.isLt).2 ho)

end Ctx

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Ctx.completeSeq_validSeq := @BCFGJPSSV26.Greedy.Ctx.completeSeq_validSeq
