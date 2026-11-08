-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_zero_nu_original_variable_stopped_gaussian_sum_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:31:40.468097+00:00
-- url     : https://prove2.me/submissions/84cb57c8-90d1-42ab-a157-854cd9d1ab66

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_variable_stopped_predictable_linear_L1_sum_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Eliminate auxiliary Lévy components from the original variable-stopped
Gaussian finite-grid mean-zero result when the actual negative-jump measure
vanishes. The integrand uses the original physical process `X.X`. -/
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
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω *
      ((X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c) -
       (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c))) P) :
    Integrable (fun ω => ∑ i ∈ S, G i ω *
      ((X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c) -
       (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c))) P ∧
    (∫ ω, ∑ i ∈ S, G i ω *
      ((X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c) -
       (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c)) ∂P) = 0 := by
  have hSource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (X.X u ω - (u : ℝ) * X.c) +
        (0 : ℝ) + (0 : ℝ) :=
    Filter.Eventually.of_forall (fun ω u => by ring)
  have hGI' : ∀ i ∈ S, Integrable (fun ω => G i ω *
      ((X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
          (0 : ℝ) - (0 : ℝ)) -
       (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
          (0 : ℝ) - (0 : ℝ)))) P := by
    intro i hi
    simpa only [sub_zero] using hGI i hi
  have hmain :=
    avram_p4_a_gaussian_ae_original_variable_stopped_predictable_linear_L1_sum_mean_zero
      X X hν (fun _ _ => 0) (fun _ _ => 0) hSource S τ hτ B hbounded
      h G hGstopped hGglobal hGI'
  simpa only [sub_zero] using hmain
