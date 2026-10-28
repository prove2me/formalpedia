-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitBeforeDown_event_antitone_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:20:02.050033+00:00
-- url     : https://prove2.me/submissions/ff2475b6-65c5-474e-8f28-3d376818dfdf

import Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_event_mono_bounds
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
    {ω : Ω | twoSidedExitUpTime X (b - x) ω < twoSidedExitDownTime X (-x) ω} ⊆
      {ω : Ω | twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω} := by
  exact twoSidedExitBeforeDown_event_mono_bounds
    X (a - x) (b - x) (-x) (-x) (by linarith) le_rfl
