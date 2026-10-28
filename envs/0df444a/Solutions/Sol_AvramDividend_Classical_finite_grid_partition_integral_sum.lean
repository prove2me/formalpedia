-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_partition_integral_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:37:54.380986+00:00
-- url     : https://prove2.me/submissions/983381f0-285f-41a3-a2b2-57bbf42abaf1

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal

/-- The expectation at a finite-valued random time is the sum over its measurable fibres. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hfib : ∀ s ∈ grid, MeasurableSet {ω : Ω | τ ω = s})
    (f : ℝ≥0 → Ω → ℝ)
    (hint : ∀ s ∈ grid, Integrable (f s) P) :
    ∫ ω, f (τ ω) ω ∂P =
      ∑ s ∈ grid, ∫ ω,
        ({ω : Ω | τ ω = s}).indicator (f s) ω ∂P := by
  classical
  have hintPart : ∀ s ∈ grid,
      Integrable (({ω : Ω | τ ω = s}).indicator (f s)) P := by
    intro s hs
    exact Integrable.indicator (hint s hs) (hfib s hs)
  have hfun : (fun ω => f (τ ω) ω) =
      (fun ω => ∑ s ∈ grid,
        ({ω : Ω | τ ω = s}).indicator (f s) ω) := by
    funext ω
    simp [Set.indicator, hgrid ω, eq_comm]
  rw [hfun]
  exact integral_finset_sum grid hintPart
