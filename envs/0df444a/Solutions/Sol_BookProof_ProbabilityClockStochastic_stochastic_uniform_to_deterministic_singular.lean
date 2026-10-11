-- Prove2me | solution 1 for BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_singular
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:06:17.702103+00:00
-- url     : https://prove2.me/submissions/b29ff6fc-edbf-4559-962e-ae1d6563adb7

-- Generated from ChapterProbabilityClockStochastic.lean — solution of BookProof.ProbabilityClockStochastic.stochastic_uniform_to_deterministic_singular
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
open BookProof.ProbabilityClockStochastic




open Matrix
open scoped Norms.Operator

set_option maxHeartbeats 1000000 in
theorem solution
    {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : IsColumnStochastic M)
    (hMap : M.mulVec ![1 / 2, 1 / 2] = ![1, 0]) : M.det = 0 := by

  obtain ⟨hnn, _⟩ := hM
  have e1 : M 1 0 * (1 / 2) + M 1 1 * (1 / 2) = 0 := by
    have h := congrFun hMap 1
    simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail] at h
    linarith [h]
  have h10 : M 1 0 = 0 := by linarith [hnn 1 0, hnn 1 1]
  have h11 : M 1 1 = 0 := by linarith [hnn 1 0, hnn 1 1]
  rw [Matrix.det_fin_two, h10, h11]; ring
