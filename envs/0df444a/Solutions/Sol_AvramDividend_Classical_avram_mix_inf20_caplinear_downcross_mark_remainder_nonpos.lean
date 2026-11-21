-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_caplinear_downcross_mark_remainder_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:38:06.393444+00:00
-- url     : https://prove2.me/submissions/93ba2464-c2de-4f52-945f-75fe004f5c97

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB31_interior_caplinear_affine_upper_derivatives
open Filter Set AvramDividend.Classical
noncomputable section
set_option autoImplicit false

theorem solution
    (w : ℝ → ℝ) (b y z : ℝ)
    (hy : b < y) (hz : y + z ≤ b)
    (hSlope : w (y + z) - w b ≤ y + z - b) :
    let V : ℝ → ℝ := fun t => if t ≤ b then w t else w b + (t - b)
    V (y + z) - V y - deriv V y * z ≤ 0 := by
  dsimp only
  have hd :
      deriv (fun t : ℝ => if t ≤ b then w t else w b + (t - b)) y = 1 :=
    (avram_gbB31_interior_caplinear_affine_upper_derivatives w b y hy).1
  rw [if_pos hz, if_neg (not_le.mpr hy), hd]
  linarith
