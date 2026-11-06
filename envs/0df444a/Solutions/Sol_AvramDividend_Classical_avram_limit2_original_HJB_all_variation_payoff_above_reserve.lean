-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_HJB_all_variation_payoff_above_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:30:33.731201+00:00
-- url     : https://prove2.me/submissions/5d519935-6479-4112-a17b-c4f8fd3ff33e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_hjb_max_to_original_source_signs
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_C1_closed_cap_payoff_above_reserve
import Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_C2_closed_cap_payoff_above_reserve
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A single HJB maximum certificate yields a quantitative candidate
    floor throughout the original BV/UBV closed-cap reserve space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwBV : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwUBV : ¬ X.BoundedVariation →
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwHJB : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → y ≤ w y := by
  obtain ⟨_, hGrad⟩ :=
    avram_limit2_bv_hjb_max_to_original_source_signs X q w C hwHJB
  by_cases hBV : X.BoundedVariation
  · exact avram_limit2_bv_C1_closed_cap_payoff_above_reserve
      C hC w hw0 hwCont (hwBV hBV) hGrad
  · exact avram_limit2_ubv_C2_closed_cap_payoff_above_reserve
      C w hw0 hwCont (hwUBV hBV) hGrad
