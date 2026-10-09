-- Prove2me | solution 1 for BookProof.ChapterEulerDensityMatrix.clockPsi_normSq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:45:16.824689+00:00
-- url     : https://prove2.me/submissions/638023ba-8930-4ce7-b779-ecbb3efec2d3

-- Generated from ChapterEulerDensityMatrix.lean — solution of BookProof.ChapterEulerDensityMatrix.clockPsi_normSq
import Mathlib
import Definitions.Def_ChapterEulerDensityMatrix
open BookProof.ChapterEulerDensityMatrix



open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) : clockPsi t ⬝ᵥ clockPsi t = 1 := by

  simp only [clockPsi, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  nlinarith [Real.sin_sq_add_cos_sq t]
