-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_original_hjb_initial_payoff_nonnegative_at_closed_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:19:46.643506+00:00
-- url     : https://prove2.me/submissions/dd5b4a1e-e45e-4bbf-b33d-204b0c35c7b2

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original verification candidate is nonnegative at the initial capped
reserve even when the initial reserve equals the finite cap. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) :
    0 ≤ w x := by
  have hC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.of_le (by norm_num)
  have hEnv := avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
    C hC w hw_cont hC1 hw_grad x (le_of_lt hx) hxc
  have hBound : w 0 + x ≤ w x :=
    hEnv x ⟨le_of_lt hx, le_rfl⟩
  linarith
