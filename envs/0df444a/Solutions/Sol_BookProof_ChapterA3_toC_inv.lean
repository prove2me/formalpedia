-- Prove2me | solution 1 for BookProof.ChapterA3.toC_inv
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:28:17.147777+00:00
-- url     : https://prove2.me/submissions/2288add4-90d7-4c26-94d5-9aac6f02b578

import Mathlib
import Definitions.Def_ChapterA3b
open BookProof.ChapterA3 Matrix
set_option autoImplicit false

theorem solution (M : Matrix (Fin 4) (Fin 4) ℝ) : toC M⁻¹ = (toC M)⁻¹ := by
  change Complex.ofRealHom.mapMatrix M⁻¹ = (Complex.ofRealHom.mapMatrix M)⁻¹
  by_cases h : IsUnit M.det
  · symm
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, Matrix.nonsing_inv_mul M h, map_one]
  · have hz : M.det = 0 := by simpa only [isUnit_iff_ne_zero, not_not] using h
    have hc : (Complex.ofRealHom.mapMatrix M).det = 0 := by
      rw [← RingHom.map_det, hz, map_zero]
    rw [Matrix.nonsing_inv_apply_not_isUnit M h,
      Matrix.nonsing_inv_apply_not_isUnit _ (by
        intro hu
        exact (isUnit_iff_ne_zero.mp hu) hc), map_zero]

#print axioms solution
