-- Prove2me | solution 1 for AvramDividend.Classical.finiteGrid_stoppedEvent_measure_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:28:13.985149+00:00
-- url     : https://prove2.me/submissions/373bee3d-d946-4462-ab6e-473fcabc1391

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedReward_lintegral_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-- The measure of a stopped event is the sum of its disjoint adapted grid-fibre masses. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τn : Ω → ℝ≥0) (A : Set Ω)
    (grid : Finset ℝ≥0) (hgrid : ∀ ω, τn ω ∈ grid)
    (hA : MeasurableSet A)
    (hfibres : ∀ s ∈ grid,
      MeasurableSet {ω : Ω | τn ω = s}) :
    P A = ∑ s ∈ grid, P (A ∩ {ω : Ω | τn ω = s}) := by
  have hInt := finiteGrid_stoppedReward_lintegral_decomposition
    P τn A grid hgrid (fun _ _ => (1 : ℝ≥0∞))
    (by
      intro s hs
      exact measurable_const.indicator (hA.inter (hfibres s hs)))
  calc
    P A = ∫⁻ ω, Set.indicator A (fun _ : Ω => (1 : ℝ≥0∞)) ω ∂P :=
      (lintegral_indicator_one hA).symm
    _ = ∑ s ∈ grid, ∫⁻ ω,
      Set.indicator (A ∩ {ω' : Ω | τn ω' = s})
        (fun _ : Ω => (1 : ℝ≥0∞)) ω ∂P := hInt
    _ = ∑ s ∈ grid, P (A ∩ {ω : Ω | τn ω = s}) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact lintegral_indicator_one (hA.inter (hfibres s hs))