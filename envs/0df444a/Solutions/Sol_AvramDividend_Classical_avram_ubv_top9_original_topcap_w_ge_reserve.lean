-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_topcap_w_ge_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:57:55.608176+00:00
-- url     : https://prove2.me/submissions/724e7a8e-fb52-4bed-b7cf-c5a48549e55c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_infinite_cap_gradient_global_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original topcap HJB derivative and zero-value assumptions force
candidate value to dominate every nonnegative starting surplus. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y : ℝ) (hy : 0 ≤ y) :
    y ≤ w y := by
  have hSmooth1 : ContDiffOn ℝ 1 w {z : ℝ | 0 < z} := by
    have hmono : ContDiffOn ℝ 1 w
        {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} :=
      hw_smooth.of_le (by norm_num)
    simpa [hTop] using hmono
  have hGrad : ∀ z : ℝ, 0 < z → 1 ≤ deriv w z := by
    intro z hz
    exact hw_grad z hz (by simp [hTop])
  have hSec := avram_wave5_04b_infinite_cap_gradient_global_secant
    w hw_cont hSmooth1 hGrad 0 y (le_refl 0) hy
  linarith
