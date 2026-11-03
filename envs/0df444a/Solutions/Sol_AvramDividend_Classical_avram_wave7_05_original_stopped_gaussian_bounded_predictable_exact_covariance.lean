-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_original_stopped_gaussian_bounded_predictable_exact_covariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:45:53.958927+00:00
-- url     : https://prove2.me/submissions/277ee4ae-b965-4286-8c1b-19382209f0a3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable

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
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hHstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGglobal : Measurable G) (hHglobal : Measurable H)
    (BG BH : ℝ) (hBG : 0 ≤ BG) (hBH : 0 ≤ BH)
    (hGbound : ∀ ω, |G ω| ≤ BG)
    (hHbound : ∀ ω, |H ω| ≤ BH) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    Integrable (fun ω => (G ω * Y ω) * (H ω * Y ω)) P ∧
      (∫ ω, (G ω * Y ω) * (H ω * Y ω) ∂P) =
        ((h : ℝ) * X.σ ^ 2) * (∫ ω, G ω * H ω ∂P) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hBase :=
    avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
      X hν τ hτ T hbounded h G H hGstop hHstop hGglobal hHglobal
        BG BH hBG hBH hGbound hHbound
  dsimp only at hBase
  have hCellI :
      Integrable (fun ω => (G ω * Y ω) * (H ω * Y ω)) P :=
    hBase.1
  have hCE :
      P[(fun ω => (G ω * Y ω) * (H ω * Y ω)) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun ω => ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) :=
    hBase.2
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
      integral_congr_ae hCE
    _ = ((h : ℝ) * X.σ ^ 2) * (∫ ω, G ω * H ω ∂P) := by
      rw [integral_const_mul]
