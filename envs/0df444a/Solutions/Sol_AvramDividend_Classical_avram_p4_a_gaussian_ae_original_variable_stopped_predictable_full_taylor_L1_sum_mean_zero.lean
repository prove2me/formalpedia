-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_original_variable_stopped_predictable_full_taylor_L1_sum_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:51:23.837749+00:00
-- url     : https://prove2.me/submissions/bb8c805e-8d54-4443-8d41-e7701ddd9ff3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_variable_stopped_predictable_linear_L1_sum_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_variable_stopped_predictable_quadratic_L1_sum_mean_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine variable-stop finite Gaussian stochastic Taylor sums for X have
zero expected centred residual, with the exact sigma-squared half-correction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hGstopped : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (G i))
    (hHstopped : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (H i))
    (hGglobal : ∀ i ∈ S, Measurable (G i))
    (hHglobal : ∀ i ∈ S, Measurable (H i))
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω *
      ((X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
          Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
       (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
          Jsmall (τ i ω) ω - Jlarge (τ i ω) ω))) P)
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S, Integrable (fun ω => H i ω *
      (((X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
          Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
       (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
          Jsmall (τ i ω) ω - Jlarge (τ i ω) ω)) ^ 2)) P) :
    let M : ι → Ω → ℝ := fun i ω =>
      (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
        Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
      (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
        Jsmall (τ i ω) ω - Jlarge (τ i ω) ω)
    Integrable (fun ω => ∑ i ∈ S,
      (G i ω * M i ω + (1 / 2 : ℝ) * H i ω *
        (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))) P ∧
      (∫ ω, (∑ i ∈ S,
        (G i ω * M i ω + (1 / 2 : ℝ) * H i ω *
          (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))) ∂P) = 0 := by
  let M : ι → Ω → ℝ := fun i ω =>
    (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
      Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
    (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
      Jsmall (τ i ω) ω - Jlarge (τ i ω) ω)
  have hL :=
    avram_p4_a_gaussian_ae_original_variable_stopped_predictable_linear_L1_sum_mean_zero
      X Y hYν Jsmall Jlarge hSourceDecomp S τ hτ B hbounded h
      G hGstopped hGglobal hGI
  have hQ :=
    avram_p4_a_gaussian_ae_original_variable_stopped_predictable_quadratic_L1_sum_mean_zero
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp S τ hτ B hbounded h
      H hHstopped hHglobal hHI hH2I
  have hSum (ω : Ω) :
      (∑ i ∈ S, (G i ω * M i ω + (1 / 2 : ℝ) * H i ω *
        (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))) =
      (∑ i ∈ S, G i ω * M i ω) +
        (1 / 2 : ℝ) * (∑ i ∈ S, H i ω *
          (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    simp only [mul_assoc]
  have hFun : (fun ω => ∑ i ∈ S, (G i ω * M i ω +
      (1 / 2 : ℝ) * H i ω * (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))) =
      (fun ω => (∑ i ∈ S, G i ω * M i ω) +
        (1 / 2 : ℝ) * (∑ i ∈ S, H i ω *
          (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))) := funext hSum
  change Integrable (fun ω => ∑ i ∈ S, (G i ω * M i ω +
      (1 / 2 : ℝ) * H i ω * (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))) P ∧
      (∫ ω, (∑ i ∈ S, (G i ω * M i ω +
        (1 / 2 : ℝ) * H i ω * (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))) ∂P) = 0
  rw [hFun]
  constructor
  · exact hL.1.add (hQ.1.const_mul (1 / 2 : ℝ))
  · rw [integral_add hL.1 (hQ.1.const_mul (1 / 2 : ℝ)),
      integral_const_mul, hL.2, hQ.2]
    ring
