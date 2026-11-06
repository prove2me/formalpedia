-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_ubv_C2_closed_cap_payoff_above_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:22:23.457194+00:00
-- url     : https://prove2.me/submissions/0ad857ed-9114-48ce-8514-3ffff77943af

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exact UBV C2 closed-cap secant bound controls the candidate by
    the physical reserve from below, including zero and an infinite cap. -/
theorem solution
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwSmooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → y ≤ w y := by
  intro y hy hyC
  have hSec :=
    avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
      C w hwCont hwSmooth hwGrad 0 y (le_refl _) hy hyC
  linarith only [hSec, hw0]
