-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_original_variable_stopped_predictable_linear_L1_sum_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:13:22.05976+00:00
-- url     : https://prove2.me/submissions/4b210b04-6856-4690-bacc-3d075e23b5ab

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_mean_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Any finite genuine stopped mesh of original Levy Gaussian predictable
linear residuals is L1 and has total expectation zero from individual
source-integrable cells; sigma may vanish and the weights need not be bounded. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G : ι → Ω → ℝ)
    (hGstopped : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (G i))
    (hGglobal : ∀ i ∈ S, Measurable (G i))
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω *
      ((X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
          Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
       (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
          Jsmall (τ i ω) ω - Jlarge (τ i ω) ω))) P) :
    let M : ι → Ω → ℝ := fun i ω =>
      (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
        Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
      (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
        Jsmall (τ i ω) ω - Jlarge (τ i ω) ω)
    Integrable (fun ω => ∑ i ∈ S, G i ω * M i ω) P ∧
      (∫ ω, ∑ i ∈ S, G i ω * M i ω ∂P) = 0 := by
  let M : ι → Ω → ℝ := fun i ω =>
    (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
      Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
    (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
      Jsmall (τ i ω) ω - Jlarge (τ i ω) ω)
  let MY : ι → Ω → ℝ := fun i ω =>
    Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
  have hAE (i : ι) : (fun ω => G i ω * M i ω) =ᵐ[P]
      (fun ω => G i ω * MY i ω) := by
    filter_upwards [hSourceDecomp] with ω hw
    dsimp [M, MY]
    rw [hw (τ i ω + h i), hw (τ i ω)]
    push_cast
    ring
  have hInt : ∀ i ∈ S, Integrable (fun ω => G i ω * M i ω) P := by
    intro i hi
    exact hGI i hi
  have hMean : ∀ i ∈ S, (∫ ω, G i ω * M i ω ∂P) = 0 := by
    intro i hi
    have hYMean :=
      avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_mean_zero
        Y hYν (τ i) (hτ i hi) (B i) (hbounded i hi) (h i)
        (G i) (hGstopped i hi) (hGglobal i hi)
    exact (integral_congr_ae (hAE i)).trans hYMean
  change Integrable (fun ω => ∑ i ∈ S, G i ω * M i ω) P ∧
    (∫ ω, ∑ i ∈ S, G i ω * M i ω ∂P) = 0
  constructor
  · exact integrable_finset_sum S (fun i hi => hInt i hi)
  · rw [integral_finset_sum S (fun i hi => hInt i hi)]
    exact Finset.sum_eq_zero (fun i hi => hMean i hi)
