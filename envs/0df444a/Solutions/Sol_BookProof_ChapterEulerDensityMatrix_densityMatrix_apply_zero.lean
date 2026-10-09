-- Prove2me | solution 1 for BookProof.ChapterEulerDensityMatrix.densityMatrix_apply_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:45:31.066164+00:00
-- url     : https://prove2.me/submissions/468fd5ae-704a-45e0-9db8-13772fc5ce6e

-- Generated from ChapterEulerDensityMatrix.lean — solution of BookProof.ChapterEulerDensityMatrix.densityMatrix_apply_zero
import Mathlib
import Definitions.Def_ChapterEulerDensityMatrix
import Theorems.Thm_BookProof_ChapterEulerDensityMatrix_densityMatrix_eq
open BookProof.ChapterEulerDensityMatrix



open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) : densityMatrix t 0 0 = Real.cos t ^ 2 := by

  rw [densityMatrix_eq]; simp
