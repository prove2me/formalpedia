-- Prove2me | solution 1 for BookProof.ChapterEulerDensityMatrix.densityMatrix_trace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:47:00.612005+00:00
-- url     : https://prove2.me/submissions/cd48a8d2-7e35-4684-b116-f3c6ac8f768f

-- Generated from ChapterEulerDensityMatrix.lean — solution of BookProof.ChapterEulerDensityMatrix.densityMatrix_trace
import Mathlib
import Definitions.Def_ChapterEulerDensityMatrix
import Theorems.Thm_BookProof_ChapterEulerDensityMatrix_densityMatrix_eq
open BookProof.ChapterEulerDensityMatrix



open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) : Matrix.trace (densityMatrix t) = 1 := by

  simp [densityMatrix_eq, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
