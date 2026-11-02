-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_grid_compensated_quadratic_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:20:42.328216+00:00
-- url     : https://prove2.me/submissions/81ea8e57-9f66-4b52-adaa-fd2e073472c4

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_compensated_square_test_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

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
      (fun ω => H i ω * (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ^ 2) P) :
    Integrable (fun ω => ∑ i ∈ S, H i ω *
      ((X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ^ 2 -
        (h i : ℝ) * X.σ ^ 2)) P ∧
    (∫ ω, ∑ i ∈ S, H i ω *
      ((X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ^ 2 -
        (h i : ℝ) * X.σ ^ 2) ∂P) = 0 := by
  classical
  let F : ι → Ω → ℝ := fun i ω => H i ω *
    ((X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ^ 2 -
      (h i : ℝ) * X.σ ^ 2)
  have hCell (i : ι) (hi : i ∈ S) :
      Integrable (F i) P ∧ (∫ ω, F i ω ∂P) = 0 := by
    simpa only [F] using
      (avram_wave6_03_original_rightCont_stopped_gaussian_compensated_square_test_zero
        X hν (τ i) (hτ i) (T i) (hbounded i hi)
        (h i) (H i) (hHstop i) (hHglobal i hi) (hHI i hi) (hWeightedInt i hi))
  have hEach : ∀ i ∈ S, Integrable (F i) P := by
    intro i hi
    exact (hCell i hi).1
  change Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
    (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0
  constructor
  · exact integrable_finset_sum S hEach
  · rw [integral_finset_sum S hEach]
    exact Finset.sum_eq_zero (fun i hi => (hCell i hi).2)
