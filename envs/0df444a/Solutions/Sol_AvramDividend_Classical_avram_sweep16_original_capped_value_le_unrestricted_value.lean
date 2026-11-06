-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_capped_value_le_unrestricted_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:10:59.082675+00:00
-- url     : https://prove2.me/submissions/e043b6f7-a26c-4469-9680-c3e20440e3da

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/- Any original capped admissible strategy remains unrestricted admissible. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (C : ℝ≥0∞) :
    valueFunctionLe X q C x ≤ valueFunction X q x := by
  unfold valueFunctionLe valueFunction
  apply iSup_le
  intro D
  apply iSup_le
  intro hD
  exact le_iSup_of_le D (le_iSup_of_le hD.1 (le_refl _))
