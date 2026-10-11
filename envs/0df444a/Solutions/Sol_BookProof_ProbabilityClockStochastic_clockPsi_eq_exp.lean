-- Prove2me | solution 1 for BookProof.ProbabilityClockStochastic.clockPsi_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:07:31.335315+00:00
-- url     : https://prove2.me/submissions/1cf1dedb-83e7-41da-8a79-82e961c5278f

-- Generated from ChapterProbabilityClockStochastic.lean — solution of BookProof.ProbabilityClockStochastic.clockPsi_eq_exp
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
import Theorems.Thm_BookProof_ProbabilityClockStochastic_rotMat_eq_exp
import Definitions.Def_ChapterEulerDensityMatrix
import Definitions.Def_ChapterEulerGenericDensity
import Definitions.Def_ChapterFullQuadraticEsa
open BookProof.ProbabilityClockStochastic




open Matrix
open scoped Norms.Operator

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) :
    (NormedSpace.exp (t • Jgen)).mulVec ![1, 0] = clockPsi t := by

  rw [rotMat_eq_exp]
  funext i
  fin_cases i <;>
    simp [rotMat, clockPsi, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
