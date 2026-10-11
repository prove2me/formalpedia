-- Prove2me | solution 1 for BookProof.ProbabilityClockStochastic.preserves_prob_iff_isColumnStochastic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:56.488729+00:00
-- url     : https://prove2.me/submissions/f244424e-64d6-44f0-9ed4-41f69b0dad64

-- Generated from ChapterProbabilityClockStochastic.lean — solution of BookProof.ProbabilityClockStochastic.preserves_prob_iff_isColumnStochastic
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
import Theorems.Thm_BookProof_ProbabilityClockStochastic_IsColumnStochastic_mulVec_isProbabilityVector
open BookProof.ProbabilityClockStochastic




open Matrix
open scoped Norms.Operator

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ v, IsProbabilityVector v → IsProbabilityVector (M.mulVec v))
      ↔ IsColumnStochastic M := by

  constructor
  · intro h
    have hb : ∀ j : Fin 2, IsProbabilityVector (Pi.single j 1) := fun j =>
      ⟨fun k => by rw [Pi.single_apply]; split <;> norm_num, by simp⟩
    refine ⟨?_, ?_⟩
    · intro i j
      have := (h _ (hb j)).1 i
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq] using this
    · intro j
      have := (h _ (hb j)).2
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq,
        Finset.sum_comm] using this
  · intro hM v hv; exact hM.mulVec_isProbabilityVector hv
