-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_ubv_zero_reserve_uniform_all_caps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:54:57.451064+00:00
-- url     : https://prove2.me/submissions/9cec1ed1-66f0-401c-a19d-caa21d75513b

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

/- Original UBV verification at zero reserve needs only w(0) ≥ 0, and holds
   for every cap simultaneously, including the unrestricted cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (q : ℝ)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0) :
    (∀ C : ℝ≥0∞,
      valueFunctionLe X q C 0 ≤ ENNReal.ofReal (w 0)) ∧
    valueFunction X q 0 ≤ ENNReal.ofReal (w 0) := by
  have hAll : ∀ C : ℝ≥0∞,
      valueFunctionLe X q C 0 ≤ ENNReal.ofReal (w 0) := by
    intro C
    rw [(avram_wave6_10_ubv_original_zero_capital_exact_zero_reward_and_value
      X hBV q C).2]
    exact bot_le
  refine ⟨hAll, ?_⟩
  simpa only [valueFunctionLe_top_eq_valueFunction] using hAll (⊤ : ℝ≥0∞)
