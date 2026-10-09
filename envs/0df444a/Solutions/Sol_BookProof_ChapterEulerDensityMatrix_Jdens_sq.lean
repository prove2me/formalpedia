-- Prove2me | solution 1 for BookProof.ChapterEulerDensityMatrix.Jdens_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:46:20.561544+00:00
-- url     : https://prove2.me/submissions/ee9d8e3a-3993-4e20-8370-796b23cdaa86

-- Generated from ChapterEulerDensityMatrix.lean — solution of BookProof.ChapterEulerDensityMatrix.Jdens_sq
import Mathlib
import Definitions.Def_ChapterEulerDensityMatrix
open BookProof.ChapterEulerDensityMatrix



open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem solution : Jdens * Jdens = -1 := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Jdens, Matrix.mul_apply, Fin.sum_univ_two]
