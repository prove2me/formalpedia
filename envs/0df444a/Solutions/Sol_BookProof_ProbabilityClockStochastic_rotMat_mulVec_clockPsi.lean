-- Prove2me | solution 1 for BookProof.ProbabilityClockStochastic.rotMat_mulVec_clockPsi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:06:47.852629+00:00
-- url     : https://prove2.me/submissions/8b3f3619-0d42-4d12-bdc5-9799ac5d5c72

-- Generated from ChapterProbabilityClockStochastic.lean — solution of BookProof.ProbabilityClockStochastic.rotMat_mulVec_clockPsi
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
import Definitions.Def_ChapterEulerDensityMatrix
import Definitions.Def_ChapterFullQuadraticEsa
open BookProof.ProbabilityClockStochastic




open Matrix
open scoped Norms.Operator

set_option maxHeartbeats 1000000 in
theorem solution (t a : ℝ) :
    (rotMat a).mulVec (clockPsi t) = clockPsi (t + a) := by

  funext i
  fin_cases i <;>
    simp [rotMat, clockPsi, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Real.cos_add, Real.sin_add] <;> ring
