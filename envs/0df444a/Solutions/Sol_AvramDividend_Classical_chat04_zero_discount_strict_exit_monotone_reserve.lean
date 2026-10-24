-- Prove2me | solution 1 for AvramDividend.Classical.chat04_zero_discount_strict_exit_monotone_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:13:49.358996+00:00
-- url     : https://prove2.me/submissions/a765c4f3-9640-4ad7-8ef9-3e6a2cb3fd3a

import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_zero_discount_eq_event_measure
import Theorems.Thm_AvramDividend_Classical_chat04_strict_up_before_ruin_event_monotone_reserve
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The successful strict two-sided exit probability grows with starting capital. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a x y : ℝ) (hxy : x ≤ y) :
    twoSidedExitExpectation X 0 a x ≤ twoSidedExitExpectation X 0 a y := by
  calc
    twoSidedExitExpectation X 0 a x =
        P {ω : Ω | twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω} :=
          chat04_twoSidedExitExpectation_zero_discount_eq_event_measure X a x
    _ ≤ P {ω : Ω | twoSidedExitUpTime X (a - y) ω <
          twoSidedExitDownTime X (-y) ω} :=
          measure_mono
            (chat04_strict_up_before_ruin_event_monotone_reserve X a x y hxy)
    _ = twoSidedExitExpectation X 0 a y :=
          (chat04_twoSidedExitExpectation_zero_discount_eq_event_measure X a y).symm
