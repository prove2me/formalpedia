-- Prove2me | solution 1 for AvramDividend.Classical.finiteGrid_stoppedReward_lintegral_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:09:15.511576+00:00
-- url     : https://prove2.me/submissions/08a2fc6b-a4c6-467f-b7f1-73f137bb9d43

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedReward_fibre_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators

/-- The nonnegative integral of a finite stopped reward is the sum over disjoint stopping-time fibres. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τn : Ω → ℝ≥0) (A : Set Ω)
    (grid : Finset ℝ≥0) (hgrid : ∀ ω, τn ω ∈ grid)
    (f : ℝ≥0 → Ω → ℝ≥0∞)
    (hMeas : ∀ s ∈ grid,
      Measurable (Set.indicator (A ∩ {ω' : Ω | τn ω' = s}) (f s))) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => f (τn ω') ω') ω ∂P) =
      ∑ s ∈ grid, ∫⁻ ω,
        Set.indicator (A ∩ {ω' : Ω | τn ω' = s}) (f s) ω ∂P := by
  classical
  have hpoint : ∀ ω : Ω,
      Set.indicator A (fun ω' : Ω => f (τn ω') ω') ω =
        ∑ s ∈ grid,
          Set.indicator (A ∩ {ω' : Ω | τn ω' = s}) (f s) ω := by
    intro ω
    exact (AvramDividend.Classical.finiteGrid_stoppedReward_fibre_decomposition
      τn A grid hgrid f ω).symm
  simp_rw [hpoint]
  rw [lintegral_finset_sum]
  intro s hs
  exact hMeas s hs