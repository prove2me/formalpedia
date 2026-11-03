-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_original_stopped_gaussian_bilinear_exact_expected_covariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:47:31.091729+00:00
-- url     : https://prove2.me/submissions/9ff38153-bdcf-48d9-a58f-9104d41f5ea3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_condExp_covariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hHstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGH : Integrable (fun ω => G ω * H ω) P)
    (hProductIntegrable : Integrable (fun ω =>
      (G ω * H ω) *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    Integrable (fun ω => (G ω * Y ω) * (H ω * Y ω)) P ∧
      (∫ ω, (G ω * Y ω) * (H ω * Y ω) ∂P) =
        ((h : ℝ) * X.σ ^ 2) * (∫ ω, G ω * H ω ∂P) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hCov :=
    avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_condExp_covariance
      X hν τ hτ B hbounded h G H hGstop hHstop hProductIntegrable
  dsimp only at hCov
  have hCov' :
      P[(fun ω => (G ω * Y ω) * (H ω * Y ω)) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun ω => ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) := by
    simpa only [Y] using hCov
  have hCellI :
      Integrable (fun ω => (G ω * Y ω) * (H ω * Y ω)) P := by
    convert hProductIntegrable using 1
    funext ω
    dsimp [Y]
    ring
  have hIntegralEq :
      (∫ ω, (P[(fun ω => (G ω * Y ω) * (H ω * Y ω)) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]) ω ∂P) =
        ∫ ω, (G ω * Y ω) * (H ω * Y ω) ∂P :=
    integral_condExp (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace_le
  change Integrable (fun ω => (G ω * Y ω) * (H ω * Y ω)) P ∧
    (∫ ω, (G ω * Y ω) * (H ω * Y ω) ∂P) =
      ((h : ℝ) * X.σ ^ 2) * (∫ ω, G ω * H ω ∂P)
  refine ⟨hCellI, ?_⟩
  calc
    (∫ ω, (G ω * Y ω) * (H ω * Y ω) ∂P) =
        ∫ ω, (P[(fun ω => (G ω * Y ω) * (H ω * Y ω)) |
          (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]) ω ∂P :=
      hIntegralEq.symm
    _ = ∫ ω, ((h : ℝ) * X.σ ^ 2) * (G ω * H ω) ∂P :=
      integral_congr_ae hCov'
    _ = ((h : ℝ) * X.σ ^ 2) * (∫ ω, G ω * H ω ∂P) := by
      rw [integral_const_mul]
