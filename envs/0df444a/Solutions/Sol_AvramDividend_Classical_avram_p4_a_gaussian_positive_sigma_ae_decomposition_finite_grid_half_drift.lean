-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_ae_decomposition_finite_grid_half_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:12:51.199985+00:00
-- url     : https://prove2.me/submissions/644dc283-ab2d-42cb-ae9f-809526e76357

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_finite_grid_half_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True finite-grid Gaussian drift for the original source residual,
conditional on an almost-sure same-path Levy-Ito decomposition. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ (u : ℝ≥0),
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (hσ : 0 < X.σ)
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
    (R : ι → Ω → ℝ)
    (hR : ∀ i ω, R i ω = X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
        Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω -
        (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
          Jsmall (τ i ω) ω - Jlarge (τ i ω) ω))
    (hWeightedInt : ∀ i ∈ S,
      Integrable (fun ω => H i ω * (R i ω) ^ 2) P) :
    Integrable (fun ω => ∑ i ∈ S,
      (1 / 2 : ℝ) * H i ω * (R i ω) ^ 2) P ∧
    (∫ ω, ∑ i ∈ S,
      (1 / 2 : ℝ) * H i ω * (R i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (((h i : ℝ) * X.σ ^ 2) / 2) * (∫ ω, H i ω ∂P) := by
  have hRes : ∀ i, R i =ᵐ[P]
      (fun ω => Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω -
        (h i : ℝ) * Y.c) := by
    intro i
    filter_upwards [hSourceDecomp] with ω hω
    rw [hR i ω, hω (τ i ω + h i), hω (τ i ω)]
    push_cast
    ring
  have hWeightedY : ∀ i ∈ S, Integrable (fun ω => H i ω *
      (Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω -
        (h i : ℝ) * Y.c) ^ 2) P := by
    intro i hi
    have hEq : (fun ω => H i ω * (R i ω) ^ 2) =ᵐ[P]
        (fun ω => H i ω * (Y.X (τ i ω + h i) ω -
          Y.X (τ i ω) ω - (h i : ℝ) * Y.c) ^ 2) := by
      filter_upwards [hRes i] with ω hiω
      rw [hiω]
    exact (hWeightedInt i hi).congr hEq
  obtain ⟨hSumY, hMeanY⟩ :=
    avram_wave6_03_original_rightCont_stopped_gaussian_predictable_finite_grid_half_drift
      Y hYν S τ hτ T hbounded h H hHstop hHglobal hHI hWeightedY
  have hSumAE :
      (fun ω : Ω => ∑ i ∈ S, (1 / 2 : ℝ) * H i ω * (R i ω) ^ 2) =ᵐ[P]
      (fun ω : Ω => ∑ i ∈ S, (1 / 2 : ℝ) * H i ω *
        (Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω -
          (h i : ℝ) * Y.c) ^ 2) := by
    filter_upwards [hSourceDecomp] with ω hω
    apply Finset.sum_congr rfl
    intro i hi
    rw [hR i ω, hω (τ i ω + h i), hω (τ i ω)]
    push_cast
    ring
  constructor
  · exact hSumY.congr hSumAE.symm
  · rw [integral_congr_ae hSumAE, hMeanY, hYσ]
