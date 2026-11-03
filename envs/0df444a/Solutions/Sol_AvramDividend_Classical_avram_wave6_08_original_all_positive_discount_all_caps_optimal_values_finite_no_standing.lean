-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_all_positive_discount_all_caps_optimal_values_finite_no_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:09:09.318201+00:00
-- url     : https://prove2.me/submissions/66a4ee09-54f3-400e-9785-efefe41d5ee7

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_theta_all_cap_and_unrestricted_optimal_value_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 < q) :
    (∀ C : ℝ≥0∞, valueFunctionLe X q C x < ⊤) ∧
      valueFunction X q x < ⊤ := by
  obtain ⟨θ, hθ, hψ⟩ :=
    avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount X q hq
  exact avram_wave6_10_original_theta_all_cap_and_unrestricted_optimal_value_finite
    X x θ hθ q (le_of_lt hψ)
