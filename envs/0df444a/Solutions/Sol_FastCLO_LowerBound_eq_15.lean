-- Prove2me | solution 1 for FastCLO.LowerBound.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:36:41.677005+00:00
-- url     : https://prove2.me/submissions/e07477d6-7134-471e-b96c-0194d5985bc1

import Mathlib
set_option autoImplicit false


theorem solution (ζ s : ℝ) (h0 : 0 ≤ ζ) (h1 : ζ < 1) (hs : 0 ≤ s) :
    Real.exp (-(2 * ζ / (1 - ζ)) * s) ≤ ((1 + ζ) / (1 - ζ)) ^ (-s) := by
  have hpos : 0 < 1 - ζ := by linarith
  have hb : 0 < (1 + ζ) / (1 - ζ) := div_pos (by linarith) hpos
  rw [Real.rpow_def_of_pos hb]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log ((1 + ζ) / (1 - ζ)) ≤ 2 * ζ / (1 - ζ) := by
    have := Real.log_le_sub_one_of_pos hb
    have e : (1 + ζ) / (1 - ζ) - 1 = 2 * ζ / (1 - ζ) := by
      field_simp; ring
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hlog hs]

