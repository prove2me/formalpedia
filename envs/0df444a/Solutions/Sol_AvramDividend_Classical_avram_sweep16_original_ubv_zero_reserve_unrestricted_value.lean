-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_ubv_zero_reserve_unrestricted_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:54:10.456509+00:00
-- url     : https://prove2.me/submissions/6f2527d5-0bc2-4943-870e-b9c9a52c4264

import Mathlib
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

/- The original unbounded-variation process ruins immediately from zero, even
   without an upper dividend cap. No verification function is required. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) :
    valueFunction X q 0 = 0 := by
  have hTop :
      valueFunctionLe X q (⊤ : ℝ≥0∞) 0 = 0 :=
    (avram_wave6_10_ubv_original_zero_capital_exact_zero_reward_and_value
      X hBV q (⊤ : ℝ≥0∞)).2
  simpa only [valueFunctionLe_top_eq_valueFunction] using hTop
