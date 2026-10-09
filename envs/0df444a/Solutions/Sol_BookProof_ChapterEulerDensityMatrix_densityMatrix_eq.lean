-- Prove2me | solution 1 for BookProof.ChapterEulerDensityMatrix.densityMatrix_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:45:29.854984+00:00
-- url     : https://prove2.me/submissions/e76275e8-8be1-443c-901c-9f1eb3c8cc07

-- Generated from ChapterEulerDensityMatrix.lean — solution of BookProof.ChapterEulerDensityMatrix.densityMatrix_eq
import Mathlib
import Definitions.Def_ChapterEulerDensityMatrix
open BookProof.ChapterEulerDensityMatrix



open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) :
    densityMatrix t =
      !![Real.cos t ^ 2, Real.cos t * Real.sin t;
         Real.cos t * Real.sin t, Real.sin t ^ 2] := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [densityMatrix, clockPsi, Matrix.vecMulVec_apply] <;> ring
