-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_all_variation_closed_cap_payoff_above_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:30:26.841066+00:00
-- url     : https://prove2.me/submissions/74149f93-df47-41f3-b1df-cfbbe27e2c89

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_C1_closed_cap_payoff_above_reserve
import Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_C2_closed_cap_payoff_above_reserve
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A single physical reserve floor for both Lévy variation branches,
    retaining exactly the branchwise interior smoothness assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwBV : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwUBV : ¬ X.BoundedVariation →
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → y ≤ w y := by
  by_cases hBV : X.BoundedVariation
  · exact avram_limit2_bv_C1_closed_cap_payoff_above_reserve
      C hC w hw0 hwCont (hwBV hBV) hwGrad
  · exact avram_limit2_ubv_C2_closed_cap_payoff_above_reserve
      C w hw0 hwCont (hwUBV hBV) hwGrad
