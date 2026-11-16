-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a548_quadratic_Gaussian_Taylor_coefficient_absolute_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:01:46.935979+00:00
-- url     : https://prove2.me/submissions/f2434e89-f96f-4f61-990d-9c75b869a2e1

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
noncomputable section

theorem solution
    (B u v z s : ℝ) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hu : |u| ≤ B) (hv : |v| ≤ B) :
    |u*z + v/2*(z^2-s)| ≤ B*(2+s)*(1+z^2) := by
  have hz0 : 0 ≤ z^2 := sq_nonneg z
  have hzabs : |z| ≤ 1+z^2 := by
    nlinarith [sq_nonneg (|z| - (1/2 : ℝ)), sq_abs z]
  have hsabs : |z^2-s| ≤ z^2+s := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hhalf : |v / 2| ≤ B / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)).mpr (by nlinarith [hv])
  have hfirst : |u*z| ≤ B*|z| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hu (abs_nonneg _)
  have hsecond : |v/2*(z^2-s)| ≤ (B/2)*(z^2+s) := by
    rw [abs_mul]
    exact (mul_le_mul hhalf hsabs (abs_nonneg _) (by positivity))
  have htri := abs_add_le (u*z) (v/2*(z^2-s))
  have habs := le_trans htri (add_le_add hfirst hsecond)
  have hBz : B*|z| ≤ B*(1+z^2) :=
    mul_le_mul_of_nonneg_left hzabs hB
  nlinarith [mul_nonneg hB hs, mul_nonneg hB hz0,
    mul_nonneg (mul_nonneg hB hs) hz0]
