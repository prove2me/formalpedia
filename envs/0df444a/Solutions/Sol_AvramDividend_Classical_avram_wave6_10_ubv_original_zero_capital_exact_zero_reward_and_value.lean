-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_10_ubv_original_zero_capital_exact_zero_reward_and_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:40:27.782087+00:00
-- url     : https://prove2.me/submissions/407b2551-5833-49c0-9a5a-085b37ed28f2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_start_dividendValue_upper
import Theorems.Thm_AvramDividend_Classical_local_verification_per_strategy_to_capped_value_bound
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
    (q : ℝ) (C : ℝ≥0∞) :
    (∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X 0 C D →
      dividendValue X q 0 D = 0) ∧
    valueFunctionLe X q C 0 = 0 := by
  have hzero : ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X 0 C D →
      dividendValue X q 0 D = 0 := by
    intro D hD
    have hbound : dividendValue X q 0 D ≤ ENNReal.ofReal (0 : ℝ) := by
      refine avram_wave6_10_ubv_original_zero_start_dividendValue_upper
        X hBV q (fun y : ℝ => y) C ?_ ?_ ?_ ?_ D hD ?_
      · norm_num
      · fun_prop
      · fun_prop
      · intro y hy hyC
        simp
      · intro ω t ht
        linarith
    apply le_antisymm
    · simpa using hbound
    · exact bot_le
  constructor
  · exact hzero
  · apply le_antisymm
    · have hcap : valueFunctionLe X q C 0 ≤ ENNReal.ofReal (0 : ℝ) := by
        apply local_verification_per_strategy_to_capped_value_bound
          X q C 0 (fun _ : ℝ => 0)
        intro D hD
        simpa using (hzero D hD).le
      simpa using hcap
    · exact bot_le
