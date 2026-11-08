-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_topcap_w_nonnegative_everywhere
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:51:18.233773+00:00
-- url     : https://prove2.me/submissions/c90b6fcf-7edd-4e39-af5a-98fb37e56abf

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_infinite_cap_gradient_global_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y : ℝ) : 0 ≤ w y := by
  by_cases hy : y < 0
  · rw [hw_neg y hy]
  · have hy0 : 0 ≤ y := le_of_not_gt hy
    have hSmooth1 : ContDiffOn ℝ 1 w {z : ℝ | 0 < z} := by
      have hmono : ContDiffOn ℝ 1 w
          {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} :=
        hw_smooth.of_le (by norm_num)
      simpa [hTop] using hmono
    have hGrad : ∀ z : ℝ, 0 < z → 1 ≤ deriv w z := by
      intro z hz
      exact hw_grad z hz (by simp [hTop])
    have hSec := avram_wave5_04b_infinite_cap_gradient_global_secant
      w hw_cont hSmooth1 hGrad 0 y (le_refl 0) hy0
    linarith
