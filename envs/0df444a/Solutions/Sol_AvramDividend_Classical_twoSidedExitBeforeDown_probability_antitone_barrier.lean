-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitBeforeDown_probability_antitone_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:20:05.419224+00:00
-- url     : https://prove2.me/submissions/7eee3928-c81e-4206-831b-2b97fd297de7

import Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_probability_mono_bounds
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Increasing the target dividend barrier decreases upper-before-ruin likelihood. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a b : ℝ) (hab : a ≤ b) :
    P {ω : Ω | twoSidedExitUpTime X (b - x) ω < twoSidedExitDownTime X (-x) ω} ≤
      P {ω : Ω | twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω} := by
  exact twoSidedExitBeforeDown_probability_mono_bounds
    X (a - x) (b - x) (-x) (-x) (by linarith) le_rfl
