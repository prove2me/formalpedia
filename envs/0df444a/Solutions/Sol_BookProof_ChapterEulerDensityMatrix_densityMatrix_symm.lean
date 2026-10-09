-- Prove2me | solution 1 for BookProof.ChapterEulerDensityMatrix.densityMatrix_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:47:13.954976+00:00
-- url     : https://prove2.me/submissions/7f3743dd-dadd-45eb-baf6-6f30ccba59e3

-- Generated from ChapterEulerDensityMatrix.lean — solution of BookProof.ChapterEulerDensityMatrix.densityMatrix_symm
import Mathlib
import Definitions.Def_ChapterEulerDensityMatrix
import Theorems.Thm_BookProof_ChapterEulerDensityMatrix_densityMatrix_eq
open BookProof.ChapterEulerDensityMatrix



open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) : (densityMatrix t)ᵀ = densityMatrix t := by

  rw [densityMatrix_eq]; ext i j; fin_cases i <;> fin_cases j <;> simp
