-- Prove2me | solution 1 for AvramDividend.Classical.chat03_upper_before_lower_passage_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T07:23:45.42983+00:00
-- url     : https://prove2.me/submissions/4155ab6e-95c6-4e2e-8e3c-58df9742b689

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The exact event that the strict upper passage precedes the strict
lower passage is Borel measurable, including infinite clock values.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) :
    MeasurableSet
      {ω : Ω | twoSidedExitUpTime X upper ω <
        twoSidedExitDownTime X lower ω} := by
  obtain ⟨hUp, hDown⟩ :=
    chat03_both_named_passage_clocks_measurable X lower upper
  exact measurableSet_lt hUp hDown
