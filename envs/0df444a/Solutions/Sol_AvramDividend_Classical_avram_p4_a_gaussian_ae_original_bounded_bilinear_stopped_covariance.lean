-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_original_bounded_bilinear_stopped_covariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:26:27.4981+00:00
-- url     : https://prove2.me/submissions/6ddccb5c-301f-459f-b44a-0482a3374b96

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The original X-minus-jumps Gaussian residual has a true bounded stopped
bilinear L¹ cell and exact conditional covariance under a single a.s.
all-time Levy-Ito decomposition; no Brownian copy is assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hHstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGglobal : Measurable G) (hHglobal : Measurable H)
    (BG BH : ℝ) (hBG : 0 ≤ BG) (hBH : 0 ≤ BH)
    (hGbound : ∀ ω, |G ω| ≤ BG)
    (hHbound : ∀ ω, |H ω| ≤ BH) :
    let M : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
        Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
          Jsmall (τ ω) ω - Jlarge (τ ω) ω)
    Integrable (fun ω => (G ω * M ω) * (H ω * M ω)) P ∧
    P[(fun ω => (G ω * M ω) * (H ω * M ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] =ᵐ[P]
      (fun ω => ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) := by
  let M : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
      Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
      (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
        Jsmall (τ ω) ω - Jlarge (τ ω) ω)
  have hRAE : M =ᵐ[P]
      (fun ω => Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c) := by
    filter_upwards [hSourceDecomp] with ω hω
    dsimp [M]
    rw [hω (τ ω + h), hω (τ ω)]
    push_cast
    ring
  obtain ⟨hProdY, hCondY⟩ :=
    avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
      Y hYν τ hτ T hbounded h G H hGstop hHstop hGglobal hHglobal
      BG BH hBG hBH hGbound hHbound
  have hProdAE :
      (fun ω => (G ω * M ω) * (H ω * M ω)) =ᵐ[P]
      (fun ω => (G ω *
        (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c)) *
        (H ω *
        (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c))) := by
    filter_upwards [hRAE] with ω hω
    rw [hω]
  change Integrable (fun ω => (G ω * M ω) * (H ω * M ω)) P ∧
    P[(fun ω => (G ω * M ω) * (H ω * M ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] =ᵐ[P]
      (fun ω => ((h : ℝ) * X.σ ^ 2) * (G ω * H ω))
  constructor
  · exact hProdY.congr hProdAE.symm
  · exact (condExp_congr_ae
      (m := (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace)
      hProdAE).trans (by simpa only [hYσ] using hCondY)
