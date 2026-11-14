-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.ValidSeq.append_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:57:29.584268+00:00
-- url     : https://prove2.me/submissions/dcefbf85-6fd2-4536-af46-352912569e86

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Openable
public import Definitions.Def_BCFGJPSSV26_Greedy_Valid
import all Definitions.Def_BCFGJPSSV26_Greedy_Valid
public import Theorems.Thm_BCFGJPSSV26_Greedy_maximal_transfer

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} (P : Par) (d : Fin n → Fin m → ℚ)

variable {P d}

/-- Appending a free atom keeps a sequence valid, without overbidding. -/
theorem ValidSeq.append_free (hP : P.Good n) (hd0 : ∀ j i, 0 ≤ d j i) {f η : ℚ} {p : ℕ}
    {pre H : List (Atom m)} (hv : ValidSeq P d f η p pre H)
    (hno : NoOver P d f (P.θseq p) (profL P.K d (pre ++ H))) {a : Atom m} (ha : a.free = true) :
    ValidSeq P d f η p pre (H ++ [a]) := by
  refine ⟨fun t ht ↦ ?_, ?_⟩
  · rw [List.length_append, List.length_singleton] at ht
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · rw [List.getElem_append_left ht, List.take_append_of_le_length ht.le]
      exact hv.1 t ht
    · rw [List.getElem_append_right le_rfl]
      exact .inl (by simpa using ha)
  · refine maximal_transfer hP hd0 (typ1 p) (θseq_pos P p) hno (fun j ↦ ?_) le_rfl hv.2
    exact profL_anti _ _ (pairs_mono (by simp)) j

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.ValidSeq.append_free := @BCFGJPSSV26.Greedy.ValidSeq.append_free
