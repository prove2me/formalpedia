-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_caplinear_upperband_mark_compensator_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:24:05.071598+00:00
-- url     : https://prove2.me/submissions/0f5dc125-9b3e-44a3-9bdf-9743162bac02

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB31_interior_caplinear_affine_upper_derivatives
open Filter Set AvramDividend.Classical
noncomputable section
set_option autoImplicit false

theorem solution
    (w : ℝ → ℝ) (b y z : ℝ)
    (hy : b < y) (hyz : b < y + z) :
    let V : ℝ → ℝ := fun t => if t ≤ b then w t else w b + (t - b)
    V (y + z) - V y - deriv V y * z = 0 := by
  dsimp only
  have hderiv :
      deriv (fun t : ℝ => if t ≤ b then w t else w b + (t - b)) y = 1 :=
    (avram_gbB31_interior_caplinear_affine_upper_derivatives w b y hy).1
  rw [if_neg (not_le.mpr hyz), if_neg (not_le.mpr hy), hderiv]
  ring
