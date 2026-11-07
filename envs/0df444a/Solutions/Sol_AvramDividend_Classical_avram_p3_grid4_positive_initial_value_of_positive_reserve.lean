-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_positive_initial_value_of_positive_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:43:12.899193+00:00
-- url     : https://prove2.me/submissions/e8aa1309-b9b4-4d3c-b1bf-7a0e6e60adae

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- At any positive capped reserve, the original candidate dominates its
nonnegative zero value plus the reserve. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Set.Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxpos : 0 < x) (hxc : ENNReal.ofReal x ≤ C) :
    0 < w x := by
  have hEnv := avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
    C hC w hw_cont hw_smooth hw_grad x hxpos.le hxc
      x (by exact ⟨hxpos.le, le_rfl⟩)
  linarith
