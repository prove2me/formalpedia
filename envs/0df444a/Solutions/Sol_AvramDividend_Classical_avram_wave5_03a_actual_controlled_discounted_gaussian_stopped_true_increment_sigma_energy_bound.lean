-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_sigma_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:47:36.026228+00:00
-- url     : https://prove2.me/submissions/9ad05f1d-ed32-4b11-a789-84654bc53b86

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_true_increment_L2_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- True original controlled stopped Gaussian increment has sigma-squared energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (s : ℝ≥0) (q K : ℝ) (hK : 0 ≤ K)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    let G : ℝ≥0 → Ω → ℝ := fun t ω =>
      let y := Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
    let H : Ω → ℝ := fun ω =>
      (Real.exp (-(q * (s : ℝ))) * X.σ) *
        max (-K) (min K (G s ω))
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    (∫ ω, (H ω * Y ω) ^ 2 ∂P) ≤
      (‖Real.exp (-(q * (s : ℝ))) * X.σ‖ * K) ^ 2 *
        ((h : ℝ) * X.σ ^ 2) := by
  classical
  let G : ℝ≥0 → Ω → ℝ := fun t ω =>
    let y := Function.leftLim
      (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
    if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
  let H : Ω → ℝ := fun ω =>
    (Real.exp (-(q * (s : ℝ))) * X.σ) *
      max (-K) (min K (G s ω))
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  change (∫ ω, (H ω * Y ω) ^ 2 ∂P) ≤
    (‖Real.exp (-(q * (s : ℝ))) * X.σ‖ * K) ^ 2 *
      ((h : ℝ) * X.σ ^ 2)
  have hG : IsStronglyPredictable 𝓕.rightCont G :=
    avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable
      X x D hD w C hw
  obtain ⟨hClip, hClipBound⟩ :=
    avram_wave3_04_clipped_stronglyPredictable_bounded G hG K hK
  have hHm : StronglyMeasurable H := by
    have hAt : StronglyMeasurable[𝓕.rightCont s] H :=
      (hClip.stronglyAdapted s).const_mul
        (Real.exp (-(q * (s : ℝ))) * X.σ)
    exact hAt.mono (𝓕.rightCont.le s)
  have hK0 : 0 ≤
      ‖Real.exp (-(q * (s : ℝ))) * X.σ‖ * K :=
    mul_nonneg (norm_nonneg _) hK
  have hBound : ∀ ω, |H ω| ≤
      ‖Real.exp (-(q * (s : ℝ))) * X.σ‖ * K := by
    intro ω
    change ‖(Real.exp (-(q * (s : ℝ))) * X.σ) *
      max (-K) (min K (G s ω))‖ ≤
      ‖Real.exp (-(q * (s : ℝ))) * X.σ‖ * K
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hClipBound s ω) (norm_nonneg _)
  have hWeighted :
      (∫ ω, (H ω * Y ω) ^ 2 ∂P) ≤
        (‖Real.exp (-(q * (s : ℝ))) * X.σ‖ * K) ^ 2 *
          (∫ ω, (Y ω) ^ 2 ∂P) := by
    simpa only [H, Y] using
      avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_true_increment_L2_bound
        X hν τ hτ T hbounded h H hHm
          (‖Real.exp (-(q * (s : ℝ))) * X.σ‖ * K)
          hK0 hBound
  have hVariance : (∫ ω, (Y ω) ^ 2 ∂P) ≤
      (h : ℝ) * X.σ ^ 2 := by
    simpa only [Y] using
      avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le
        X hν τ hτ T hbounded h
  calc
    (∫ ω, (H ω * Y ω) ^ 2 ∂P) ≤
      (‖Real.exp (-(q * (s : ℝ))) * X.σ‖ * K) ^ 2 *
        (∫ ω, (Y ω) ^ 2 ∂P) := hWeighted
    _ ≤ _ := mul_le_mul_of_nonneg_left hVariance (sq_nonneg _)
