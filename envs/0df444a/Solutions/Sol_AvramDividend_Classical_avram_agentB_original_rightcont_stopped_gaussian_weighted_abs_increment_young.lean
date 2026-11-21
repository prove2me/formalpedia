-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_original_rightcont_stopped_gaussian_weighted_abs_increment_young
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:22:32.697236+00:00
-- url     : https://prove2.me/submissions/bc10490f-2b86-4770-b8eb-83fcae87c41d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
import Theorems.Thm_AvramDividend_Classical_avram_agentB_weighted_gaussian_abs_first_from_exact_second_moment
open MeasureTheory Set Filter ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false
/-- Actual source stopped-history discounted dividend weights
obey the sharp quadratic-to-first-Gaussian root-cell Young estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτevents : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s]
      {ω : Ω | τ ω ≤ s})
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτevents).measurableSpace] H)
    (hHglobal : Measurable H)
    (hHnonneg : ∀ ω, 0 ≤ H ω)
    (hHI : Integrable H P)
    (hHZI : Integrable (fun ω => H ω * abs
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) P)
    (hHZ2I : Integrable (fun ω => H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P)
    (δ : ℝ) (hδ : 0 < δ) :
    (2 * δ) * (∫ ω, H ω *
      abs (X.X (τ ω + h) ω - X.X (τ ω) ω -
        (h : ℝ) * X.c) ∂P) ≤
    ((h : ℝ) * X.σ ^ 2 + δ ^ 2) * (∫ ω, H ω ∂P) := by
  let Z : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hFactor := avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
    X hν τ hτevents T hbounded h H hH hHglobal
  have hVar := avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
    X hν τ hτstop T hbounded h
  have hWeighted : (∫ ω, H ω * (Z ω)^2 ∂P) =
      ((h : ℝ) * X.σ ^ 2) * (∫ ω, H ω ∂P) := by
    change (∫ ω, H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) =
      ((h : ℝ) * X.σ ^ 2) * (∫ ω, H ω ∂P)
    rw [hFactor, hVar]
    ring
  exact avram_agentB_weighted_gaussian_abs_first_from_exact_second_moment
    H Z ((h : ℝ) * X.σ ^ 2) δ hδ hHnonneg hHI hHZI hHZ2I hWeighted
