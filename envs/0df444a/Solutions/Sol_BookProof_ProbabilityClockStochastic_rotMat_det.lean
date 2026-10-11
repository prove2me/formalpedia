-- Prove2me | solution 1 for BookProof.ProbabilityClockStochastic.rotMat_det
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:06:32.91697+00:00
-- url     : https://prove2.me/submissions/2e7cb2e1-3733-4f25-815f-a2a25469faa0

-- Generated from ChapterProbabilityClockStochastic.lean — solution of BookProof.ProbabilityClockStochastic.rotMat_det
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
import Definitions.Def_ChapterFullQuadraticEsa
open BookProof.ProbabilityClockStochastic




open Matrix
open scoped Norms.Operator

set_option maxHeartbeats 1000000 in
theorem solution (a : ℝ) : (rotMat a).det = 1 := by

  simp only [rotMat, Matrix.det_fin_two_of]
  nlinarith [Real.cos_sq_add_sin_sq a]
