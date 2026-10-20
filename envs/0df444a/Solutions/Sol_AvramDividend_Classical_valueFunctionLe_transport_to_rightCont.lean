-- Prove2me | solution 1 for AvramDividend.Classical.valueFunctionLe_transport_to_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:39:25.88285+00:00
-- url     : https://prove2.me/submissions/d6e7c47a-0b26-4054-b5dc-773362630410

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_admissibleLe_transport_to_rightCont
import Theorems.Thm_AvramDividend_Classical_dividendValue_transport_same_process
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕.rightCont)
    (hXY : Y.X = X.X)
    (q : ℝ) (C : ℝ≥0∞) (x : ℝ) :
    valueFunctionLe X q C x ≤ valueFunctionLe Y q C x := by
  classical
  unfold valueFunctionLe
  refine iSup_le fun D => iSup_le fun hD => ?_
  have hDY := admissibleLe_transport_to_rightCont X Y hXY x C D hD
  have hvalue : dividendValue X q x D ≤ dividendValue Y q x D :=
    le_of_eq ((dividendValue_transport_same_process X Y hXY q x D).symm)
  exact le_iSup_of_le D (le_iSup_of_le hDY hvalue)
