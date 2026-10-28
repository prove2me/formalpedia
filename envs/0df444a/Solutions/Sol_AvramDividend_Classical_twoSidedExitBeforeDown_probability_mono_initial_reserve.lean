-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitBeforeDown_probability_mono_initial_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:55:17.578773+00:00
-- url     : https://prove2.me/submissions/1f2e56df-0bea-4240-a283-6209bce73cf2

import Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_probability_mono_bounds
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Upper-first passage probability is increasing in the initial reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x y : ℝ) (hxy : x ≤ y) :
    P {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} ≤
    P {ω : Ω | twoSidedExitUpTime X (a - y) ω <
      twoSidedExitDownTime X (-y) ω} := by
  exact twoSidedExitBeforeDown_probability_mono_bounds
    X (a - y) (a - x) (-y) (-x) (by linarith) (by linarith)
