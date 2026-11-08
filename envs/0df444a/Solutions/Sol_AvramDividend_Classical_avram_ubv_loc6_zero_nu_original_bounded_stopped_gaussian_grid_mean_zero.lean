-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_zero_nu_original_bounded_stopped_gaussian_grid_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:31:45.075521+00:00
-- url     : https://prove2.me/submissions/9dcd0e05-acf6-4511-9d4f-3580283a8e3f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A finite original physical Gaussian grid with bounded stopped weights has
finite first moment and zero mean, without any additional cell-L1 hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G : ι → Ω → ℝ)
    (hGstopped : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace]
        (G i))
    (hGglobal : ∀ i ∈ S, Measurable (G i))
    (K : ι → ℝ) (hK : ∀ i ∈ S, 0 ≤ K i)
    (hGbound : ∀ i ∈ S, ∀ ω, |G i ω| ≤ K i) :
    Integrable (fun ω => ∑ i ∈ S, G i ω *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c)) P ∧
    (∫ ω, ∑ i ∈ S, G i ω *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ∂P) = 0 := by
  have hCell (i : ι) (hi : i ∈ S) :
      Integrable (fun ω => G i ω *
        (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c)) P ∧
      (∫ ω, G i ω *
        (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ∂P) = 0 := by
    exact (avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero
      X hν (τ i) (hτ i hi) (B i) (hbounded i hi)
      (h i) (G i) (hGstopped i hi) (hGglobal i hi)
      (K i) (hK i hi) (hGbound i hi)).2
  constructor
  · exact integrable_finset_sum S (fun i hi => (hCell i hi).1)
  · rw [integral_finset_sum S (fun i hi => (hCell i hi).1)]
    exact Finset.sum_eq_zero (fun i hi => (hCell i hi).2)
