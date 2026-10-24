-- Prove2me | solution 1 for AvramDividend.Classical.chat04_twoSidedExitExpectation_le_upperfirst_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:21:29.710406+00:00
-- url     : https://prove2.me/submissions/a8f014e2-53e9-4a61-9b4e-497f0955bf99

import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_antitone_discount
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_zero_discount_eq_event_measure
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The discounted killed reward is bounded by the exact
strict upward-before-ruin success probability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) (hq : 0 ≤ q) :
    twoSidedExitExpectation X q a x ≤
      P {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} := by
  calc
    twoSidedExitExpectation X q a x ≤
        twoSidedExitExpectation X 0 a x :=
      chat04_twoSidedExitExpectation_antitone_discount X 0 q a x hq
    _ = P {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} :=
      chat04_twoSidedExitExpectation_zero_discount_eq_event_measure X a x
