-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_finite_grid_half_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T00:09:15.165117+00:00
-- url     : https://prove2.me/submissions/f08500d9-8913-42f3-a878-fc1fa28d4ea5

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_half_variance_drift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Finite original-source stopped Gaussian Taylor cells have the exact
predictable half-variance drift, with true L1 control. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι)
    (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i : ι, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (T : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ T i)
    (h : ι → ℝ≥0) (H : ι → Ω → ℝ)
    (hHstop : ∀ i : ι,
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i)).measurableSpace] (H i))
    (hHglobal : ∀ i ∈ S, Measurable (H i))
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hWeightedInt : ∀ i ∈ S, Integrable
      (fun ω => H i ω *
        (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ^ 2) P) :
    Integrable (fun ω => ∑ i ∈ S, (1 / 2 : ℝ) * H i ω *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ^ 2) P ∧
    (∫ ω, ∑ i ∈ S, (1 / 2 : ℝ) * H i ω *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ^ 2 ∂P) =
      ∑ i ∈ S, ((h i : ℝ) * X.σ ^ 2 / 2) * (∫ ω, H i ω ∂P) := by
  classical
  let F : ι → Ω → ℝ := fun i ω => (1 / 2 : ℝ) * H i ω *
    (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ^ 2
  have hCell (i : ι) (hi : i ∈ S) :
      Integrable (F i) P ∧
      (∫ ω, F i ω ∂P) =
        ((h i : ℝ) * X.σ ^ 2 / 2) * (∫ ω, H i ω ∂P) := by
    simpa only [F] using
      (avram_wave6_03_original_rightCont_stopped_gaussian_predictable_half_variance_drift
        X hν (τ i) (hτ i) (T i) (hbounded i hi)
        (h i) (H i) (hHstop i) (hHglobal i hi)
        (hHI i hi) (hWeightedInt i hi))
  have hEach : ∀ i ∈ S, Integrable (F i) P := by
    intro i hi
    exact (hCell i hi).1
  change Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
    (∫ ω, ∑ i ∈ S, F i ω ∂P) =
      ∑ i ∈ S, ((h i : ℝ) * X.σ ^ 2 / 2) * (∫ ω, H i ω ∂P)
  constructor
  · exact integrable_finset_sum S hEach
  · rw [integral_finset_sum S hEach]
    exact Finset.sum_congr rfl (fun i hi => (hCell i hi).2)
