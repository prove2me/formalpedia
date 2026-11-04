-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_normalized_same_source_stopped_weighted_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:30:37.547534+00:00
-- url     : https://prove2.me/submissions/d7faeccc-6ef9-4941-a941-4d631b909c85

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Conditional stopped-history quadratic energy, with original Gaussian
normalisation and exact same-path decomposition as an explicit hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (ω : Ω),
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (hσ : 0 < X.σ)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H) :
    (∫ ω, H ω * ((X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
      Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
      (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
       Jsmall (τ ω) ω - Jlarge (τ ω) ω)) / X.σ) ^ 2 ∂P) =
      (∫ ω, H ω ∂P) * (h : ℝ) := by
  have hVar :
      (∫ ω, H ω *
        (Y.X (τ ω + h) ω - Y.X (τ ω) ω -
          (h : ℝ) * Y.c) ^ 2 ∂P) =
      (∫ ω, H ω ∂P) * ((h : ℝ) * Y.σ ^ 2) :=
    avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance
      Y hYν τ hτ T hbounded h H hH hHglobal
  have hFn :
      (fun ω : Ω => H ω *
        ((X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
          Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
          (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
           Jsmall (τ ω) ω - Jlarge (τ ω) ω)) / X.σ) ^ 2) =
      (fun ω : Ω =>
        (X.σ ^ 2)⁻¹ * (H ω *
          (Y.X (τ ω + h) ω - Y.X (τ ω) ω -
            (h : ℝ) * Y.c) ^ 2)) := by
    funext ω
    rw [hSourceDecomp (τ ω + h) ω, hSourceDecomp (τ ω) ω]
    push_cast
    ring
  rw [hFn, integral_const_mul, hVar, hYσ]
  field_simp [ne_of_gt hσ]
