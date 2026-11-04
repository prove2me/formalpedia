-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_original_residual_finite_grid_half_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:54:30.605469+00:00
-- url     : https://prove2.me/submissions/9aa8f272-9f7e-4466-ba08-65d6e49e83fb

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
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
conditional on an exact same-path Levy-Ito decomposition. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (ω : Ω),
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
  have hRes : ∀ i ω,
      R i ω = Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω -
        (h i : ℝ) * Y.c := by
    intro i ω
    rw [hR i ω, hSourceDecomp (τ i ω + h i) ω,
      hSourceDecomp (τ i ω) ω]
    push_cast
    ring
  have hWeightedY : ∀ i ∈ S, Integrable (fun ω => H i ω *
      (Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω -
        (h i : ℝ) * Y.c) ^ 2) P := by
    intro i hi
    simpa only [hRes i] using (hWeightedInt i hi)
  obtain ⟨hSumY, hMeanY⟩ :=
    avram_wave6_03_original_rightCont_stopped_gaussian_predictable_finite_grid_half_drift
      Y hYν S τ hτ T hbounded h H hHstop hHglobal hHI hWeightedY
  have hSumEq :
      (fun ω : Ω => ∑ i ∈ S, (1 / 2 : ℝ) * H i ω * (R i ω) ^ 2) =
      (fun ω : Ω => ∑ i ∈ S, (1 / 2 : ℝ) * H i ω *
        (Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω -
          (h i : ℝ) * Y.c) ^ 2) := by
    funext ω
    apply Finset.sum_congr rfl
    intro i hi
    rw [hRes i ω]
  constructor
  · rw [hSumEq]
    exact hSumY
  · rw [hSumEq, hMeanY, hYσ]
