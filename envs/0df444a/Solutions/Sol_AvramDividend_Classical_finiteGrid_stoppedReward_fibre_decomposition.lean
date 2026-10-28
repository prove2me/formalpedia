-- Prove2me | solution 1 for AvramDividend.Classical.finiteGrid_stoppedReward_fibre_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:51:46.812494+00:00
-- url     : https://prove2.me/submissions/493d68c0-5520-40c0-9122-bfd6a7d9601b

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Probability.Process.Stopping
import Mathlib.Algebra.Notation.Indicator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal BigOperators

/-- The killed payoff of a finite-valued stopping time is a disjoint fibre sum. -/
theorem solution
    {Ω : Type*} (τn : Ω → ℝ≥0) (A : Set Ω)
    (grid : Finset ℝ≥0) (hgrid : ∀ ω, τn ω ∈ grid)
    (f : ℝ≥0 → Ω → ℝ≥0∞) (ω : Ω) :
    (∑ s ∈ grid,
      Set.indicator (A ∩ {ω' : Ω | τn ω' = s}) (f s) ω) =
      Set.indicator A (fun ω' : Ω => f (τn ω') ω') ω := by
  classical
  by_cases hA : ω ∈ A
  · simp [Set.indicator, hA, hgrid ω]
  · simp [Set.indicator, hA]
