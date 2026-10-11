-- Prove2me | solution 1 for BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_not_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:06:31.878935+00:00
-- url     : https://prove2.me/submissions/86c50c3a-aad3-4613-bd86-6c3048421afe

-- Generated from ChapterProbabilityClockStochastic.lean — solution of BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_not_isUnit
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
import Theorems.Thm_BookProof_ProbabilityClockStochastic_stochastic_uniform_to_deterministic_singular
open BookProof.ProbabilityClockStochastic




open Matrix
open scoped Norms.Operator

set_option maxHeartbeats 1000000 in
theorem solution
    {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : IsColumnStochastic M)
    (hMap : M.mulVec ![1 / 2, 1 / 2] = ![1, 0]) : ¬ IsUnit M := by

  rw [Matrix.isUnit_iff_isUnit_det, stochastic_uniform_to_deterministic_singular hM hMap]
  simp
