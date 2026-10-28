-- Prove2me | solution 1 for AvramDividend.Classical.chat04_lower_before_upper_passage_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T12:06:42.218562+00:00
-- url     : https://prove2.me/submissions/7c2a38fc-56bc-4ba3-9ee0-46e4c66bf2ee

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- The strict lower-before-upper passage event is measurable, including infinite times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) :
    MeasurableSet
      {ω : Ω | twoSidedExitDownTime X lower ω <
        twoSidedExitUpTime X upper ω} := by
  obtain ⟨hUp, hDown⟩ :=
    chat03_both_named_passage_clocks_measurable X lower upper
  exact measurableSet_lt hDown hUp
