-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_original_bounded_bilinear_bracket_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:26:23.989936+00:00
-- url     : https://prove2.me/submissions/b1fc16bd-fecd-4222-b80e-e6f8df9d5169

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_bracket_auto_L1_condExp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The original X-minus-jumps residual has zero stopped conditional
bilinear compensated bracket under an a.s. all-time decomposition. -/
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
    (hHbound : ∀ ω, |H ω| ≤ BH)
    (hGHInt : Integrable (fun ω => G ω * H ω) P) :
    let M : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
        Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
          Jsmall (τ ω) ω - Jlarge (τ ω) ω)
    P[(fun ω => (G ω * M ω) * (H ω * M ω) -
      ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] =ᵐ[P]
      (fun _ => (0 : ℝ)) := by
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
  have hCompAE :
      (fun ω => (G ω * M ω) * (H ω * M ω) -
        ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) =ᵐ[P]
      (fun ω => (G ω *
        (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c)) *
        (H ω *
        (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c)) -
        ((h : ℝ) * Y.σ ^ 2) * (G ω * H ω)) := by
    filter_upwards [hRAE] with ω hω
    rw [hω, hYσ]
  have hCondY :=
    avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_bracket_auto_L1_condExp_zero
      Y hYν τ hτ T hbounded h G H hGstop hHstop hGglobal hHglobal
      BG BH hBG hBH hGbound hHbound hGHInt
  change P[(fun ω => (G ω * M ω) * (H ω * M ω) -
      ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] =ᵐ[P]
      (fun _ => (0 : ℝ))
  exact (condExp_congr_ae
    (m := (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace)
    hCompAE).trans hCondY
