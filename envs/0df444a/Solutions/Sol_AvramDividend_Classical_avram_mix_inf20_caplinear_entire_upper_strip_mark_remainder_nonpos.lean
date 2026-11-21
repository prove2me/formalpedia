-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_caplinear_entire_upper_strip_mark_remainder_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:43:53.060328+00:00
-- url     : https://prove2.me/submissions/93db1223-aaae-40b5-8307-4327931ce579

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_caplinear_upperband_mark_compensator_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_caplinear_downcross_mark_remainder_nonpos
open Filter Set AvramDividend.Classical
noncomputable section
set_option autoImplicit false

theorem solution
    (w : ℝ → ℝ) (b y z : ℝ)
    (hy : b < y)
    (hSlope : ∀ u : ℝ, u ≤ b → w u - w b ≤ u - b) :
    let V : ℝ → ℝ := fun t => if t ≤ b then w t else w b + (t - b)
    V (y + z) - V y - deriv V y * z ≤ 0 := by
  dsimp only
  by_cases hc : y + z ≤ b
  · exact avram_mix_inf20_caplinear_downcross_mark_remainder_nonpos
      w b y z hy hc (hSlope (y + z) hc)
  · have hUpper : b < y + z := lt_of_not_ge hc
    exact le_of_eq
      (avram_mix_inf20_original_caplinear_upperband_mark_compensator_zero
        w b y z hy hUpper)
