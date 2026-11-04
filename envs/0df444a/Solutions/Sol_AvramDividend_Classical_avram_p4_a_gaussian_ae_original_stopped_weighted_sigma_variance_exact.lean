-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_original_stopped_weighted_sigma_variance_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:47:37.16747+00:00
-- url     : https://prove2.me/submissions/2f2b28b8-14a5-4297-9022-c0d3df555dcb

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- An actual jump-bearing original Lévy residual stopped cell has exact
weighted Gaussian sigma-squared L² energy on one a.s. extraction event. -/
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
    (h : ℝ≥0) (H : Ω → ℝ)
    (hHstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H) :
    let M : Ω → ℝ := fun ω =>
      (X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
        Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω) -
      (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
        Jsmall (τ ω) ω - Jlarge (τ ω) ω)
    (∫ ω, (H ω * M ω) ^ 2 ∂P) =
      (∫ ω, (H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  let M : Ω → ℝ := fun ω =>
    (X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
      Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω) -
    (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
      Jsmall (τ ω) ω - Jlarge (τ ω) ω)
  have hAE : M =ᵐ[P]
      (fun ω => Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c) := by
    filter_upwards [hSourceDecomp] with ω hw
    dsimp [M]
    rw [hw (τ ω + h), hw (τ ω)]
    push_cast
    ring
  have hSqAE : (fun ω => (H ω * M ω) ^ 2) =ᵐ[P]
      (fun ω => (H ω *
        (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c)) ^ 2) := by
    filter_upwards [hAE] with ω he
    exact congrArg (fun z : ℝ => (H ω * z) ^ 2) he
  have hSource :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq
      Y hYν τ hτ T hbounded h H hHstop hHglobal
  change (∫ ω, (H ω * M ω) ^ 2 ∂P) =
    (∫ ω, (H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2)
  calc
    (∫ ω, (H ω * M ω) ^ 2 ∂P) =
        (∫ ω, (H ω *
          (Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c)) ^ 2 ∂P) :=
      integral_congr_ae hSqAE
    _ = (∫ ω, (H ω) ^ 2 ∂P) * ((h : ℝ) * Y.σ ^ 2) := hSource
    _ = (∫ ω, (H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2) := by rw [hYσ]
