-- Prove2me | solution 1 for AvramDividend.Classical.finiteGrid_stoppedHistory_indicator_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:51:42.591683+00:00
-- url     : https://prove2.me/submissions/b5c256b2-7761-4585-beb6-7f6f32bb19f5

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Probability.Process.Stopping
import Mathlib.Algebra.Notation.Indicator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal BigOperators

/-- A finite-valued stopping time partitions a stopped-history indicator fibrewise. -/
theorem solution
    {Ω : Type*} (τn : Ω → ℝ≥0) (A : Set Ω) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τn ω ∈ grid) (ω : Ω) :
    (∑ s ∈ grid,
      Set.indicator (A ∩ {ω' : Ω | τn ω' = s})
        (fun _ : Ω => (1 : ℝ≥0∞)) ω) =
      Set.indicator A (fun _ : Ω => (1 : ℝ≥0∞)) ω := by
  classical
  by_cases hA : ω ∈ A
  · simp [Set.indicator, hA, hgrid ω]
  · simp [Set.indicator, hA]
