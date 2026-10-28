-- Prove2me | solution 1 for AvramDividend.Classical.chat08_two_point_clock_increment_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:15:37.031421+00:00
-- url     : https://prove2.me/submissions/209480b7-e5b8-43d5-a27a-67a4ebd199d0

import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-! Split a path increment at a two-valued random clock by its observation event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℝ) (s t u : ℝ≥0) (A : Set Ω) (ω : Ω) :
    Y ((if ω ∈ A then s else t) + u) ω -
      Y (if ω ∈ A then s else t) ω =
    if ω ∈ A then Y (s + u) ω - Y s ω
      else Y (t + u) ω - Y t ω := by
  classical
  by_cases hA : ω ∈ A <;> simp [hA]
