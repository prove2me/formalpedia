-- Prove2me | solution 1 for BookProof.ChapterEulerDensityMatrix.densityMatrix_apply_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:45:44.136615+00:00
-- url     : https://prove2.me/submissions/51a34c18-7a91-4f86-9a9d-a6d39e90eaab

-- Generated from ChapterEulerDensityMatrix.lean — solution of BookProof.ChapterEulerDensityMatrix.densityMatrix_apply_one
import Mathlib
import Definitions.Def_ChapterEulerDensityMatrix
import Theorems.Thm_BookProof_ChapterEulerDensityMatrix_densityMatrix_eq
open BookProof.ChapterEulerDensityMatrix



open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) : densityMatrix t 1 1 = Real.sin t ^ 2 := by

  rw [densityMatrix_eq]; simp
