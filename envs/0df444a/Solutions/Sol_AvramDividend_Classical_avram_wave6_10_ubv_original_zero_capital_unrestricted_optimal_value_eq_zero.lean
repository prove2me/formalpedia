-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_10_ubv_original_zero_capital_unrestricted_optimal_value_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:46:07.639256+00:00
-- url     : https://prove2.me/submissions/8a87dc5f-8d5e-4614-9c30-5ffb8fb4d25b

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_capital_exact_zero_reward_and_value
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) :
    valueFunction X q 0 = 0 := by
  have hzero :=
    (avram_wave6_10_ubv_original_zero_capital_exact_zero_reward_and_value
      X hBV q (⊤ : ℝ≥0∞)).2
  simpa only [valueFunctionLe_top_eq_valueFunction] using hzero
