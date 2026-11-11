-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin22_positive_initial_from_closed_cap_gradient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:07:56.46421+00:00
-- url     : https://prove2.me/submissions/100a23a8-3206-49c3-b2e9-588f3c9daa26

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x)
    (hxc : ENNReal.ofReal x ≤ C) :
    0 ≤ w x := by
  have hC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.of_le (by norm_num)
  have henv :=
    avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
      C hC w hw_cont hC1 hw_grad x (le_of_lt hx) hxc
      x ⟨le_of_lt hx, le_refl x⟩
  linarith
