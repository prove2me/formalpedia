-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_valueFunctionLe_antitone_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:20:58.062196+00:00
-- url     : https://prove2.me/submissions/7af3c0c1-60aa-4fdd-b9a7-753df243f2cb

import Mathlib.Order.CompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_antitone_discount
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Optimising over the same capped source strategies preserves the
    comparison of the original full expected Stieltjes cash at two rates. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂) :
    valueFunctionLe X q₂ C x ≤ valueFunctionLe X q₁ C x := by
  unfold valueFunctionLe
  refine iSup_le fun D => iSup_le fun hD => ?_
  exact le_iSup_of_le D
    (le_iSup_of_le hD
      (avram_wave7_03_original_dividendValue_antitone_discount
        X x D q₁ q₂ hq))
