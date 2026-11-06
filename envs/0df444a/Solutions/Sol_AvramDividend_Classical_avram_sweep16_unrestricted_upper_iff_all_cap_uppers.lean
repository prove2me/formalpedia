-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_unrestricted_upper_iff_all_cap_uppers
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:16:00.44331+00:00
-- url     : https://prove2.me/submissions/53f02188-6976-4782-8733-4788437d9368

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_capped_value_le_unrestricted_value
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
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) (M : ℝ≥0∞) :
    (∀ C : ℝ≥0∞, valueFunctionLe X q C x ≤ M) ↔
      valueFunction X q x ≤ M := by
  constructor
  · intro hAll
    have hTop := hAll (⊤ : ℝ≥0∞)
    rw [valueFunctionLe_top_eq_valueFunction] at hTop
    exact hTop
  · intro hUpper C
    exact (avram_sweep16_original_capped_value_le_unrestricted_value X q x C).trans hUpper
