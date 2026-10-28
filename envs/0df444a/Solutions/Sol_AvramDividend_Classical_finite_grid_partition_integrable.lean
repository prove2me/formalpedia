-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_partition_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:35:57.943655+00:00
-- url     : https://prove2.me/submissions/4e2b9fd6-19de-4c54-9374-d61531e8dc6b

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Instances.NNReal.Lemmas
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal

/-- Finite measurable random-time partitions preserve integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hfib : ∀ s ∈ grid, MeasurableSet {ω : Ω | τ ω = s})
    (f : ℝ≥0 → Ω → ℝ)
    (hint : ∀ s ∈ grid, Integrable (f s) P) :
    Integrable (fun ω => f (τ ω) ω) P := by
  classical
  have hintPart : ∀ s ∈ grid,
      Integrable (({ω : Ω | τ ω = s}).indicator (f s)) P := by
    intro s hs
    exact Integrable.indicator (hint s hs) (hfib s hs)
  have hpart (ω : Ω) :
      f (τ ω) ω =
        ∑ s ∈ grid, ({ω : Ω | τ ω = s}).indicator (f s) ω := by
    simp [Set.indicator, hgrid ω, eq_comm]
  have hfun : (fun ω => f (τ ω) ω) =
      (fun ω => ∑ s ∈ grid,
        ({ω : Ω | τ ω = s}).indicator (f s) ω) := by
    funext ω
    exact hpart ω
  rw [hfun]
  exact integrable_finset_sum grid hintPart
