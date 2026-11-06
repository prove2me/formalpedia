-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_unrestricted_value_as_sup_all_caps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:10:53.95912+00:00
-- url     : https://prove2.me/submissions/a764ca19-65c8-4d3c-a40c-b65667a54f31

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
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) :
    (⨆ C : ℝ≥0∞, valueFunctionLe X q C x) = valueFunction X q x := by
  apply le_antisymm
  · apply iSup_le
    intro C
    exact avram_sweep16_original_capped_value_le_unrestricted_value X q x C
  · calc
      valueFunction X q x = valueFunctionLe X q (⊤ : ℝ≥0∞) x :=
        (valueFunctionLe_top_eq_valueFunction X q x).symm
      _ ≤ ⨆ C : ℝ≥0∞, valueFunctionLe X q C x :=
        le_iSup_of_le ⊤ (le_refl _)
