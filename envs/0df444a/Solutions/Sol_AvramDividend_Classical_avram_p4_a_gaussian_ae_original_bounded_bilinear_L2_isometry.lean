-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_original_bounded_bilinear_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:42:33.012058+00:00
-- url     : https://prove2.me/submissions/ec6f33aa-1965-4587-ba24-a0983339cda4

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_L2_covariance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The original Gaussian residual has bounded stopped weighted L² cells
and exact bilinear isometry under a single a.s. Levy-Ito extraction. -/
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
    MemLp (fun ω => G ω * M ω) 2 P ∧
    MemLp (fun ω => H ω * M ω) 2 P ∧
    (∫ ω, (G ω * M ω) * (H ω * M ω) ∂P) =
      (∫ ω, G ω * H ω ∂P) * ((h : ℝ) * X.σ ^ 2) := by
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
  obtain ⟨hGMY, hHMY, hCovY⟩ :=
    avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_L2_covariance
      Y hYν τ hτ T hbounded h G H hGstop hHstop hGglobal hHglobal
      BG BH hBG hBH hGbound hHbound
  have hGAE : (fun ω => G ω * M ω) =ᵐ[P]
      (fun ω => G ω *
        (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c)) := by
    filter_upwards [hRAE] with ω hω
    rw [hω]
  have hHAE : (fun ω => H ω * M ω) =ᵐ[P]
      (fun ω => H ω *
        (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c)) := by
    filter_upwards [hRAE] with ω hω
    rw [hω]
  have hProdAE :
      (fun ω => (G ω * M ω) * (H ω * M ω)) =ᵐ[P]
      (fun ω => (G ω *
        (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c)) *
        (H ω *
        (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c))) := by
    filter_upwards [hRAE] with ω hω
    rw [hω]
  change MemLp (fun ω => G ω * M ω) 2 P ∧
    MemLp (fun ω => H ω * M ω) 2 P ∧
    (∫ ω, (G ω * M ω) * (H ω * M ω) ∂P) =
      (∫ ω, G ω * H ω ∂P) * ((h : ℝ) * X.σ ^ 2)
  refine ⟨(memLp_congr_ae hGAE).2 hGMY,
    (memLp_congr_ae hHAE).2 hHMY, ?_⟩
  rw [integral_congr_ae hProdAE, hCovY, hYσ]
