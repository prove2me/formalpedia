-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_original_stopped_gaussian_centered_square_absolute_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:45:00.41528+00:00
-- url     : https://prove2.me/submissions/aa08ff0f-48e9-46ab-bdee-6ec784778389

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
import Theorems.Thm_AvramDividend_Classical_avram_agentB_gaussian_centered_square_abs_moment_le_twice_variance
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false
/-- True original stopped Gaussian centred square absolute residual is
controlled by twice the exact physical stopped variance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (hInt : Integrable
      (fun ω => (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    Integrable (fun ω => abs (
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 -
      (h : ℝ) * X.σ ^ 2)) P ∧
    (∫ ω, abs ((X.X (τ ω + h) ω - X.X (τ ω) ω -
      (h : ℝ) * X.c) ^ 2 - (h : ℝ) * X.σ ^ 2) ∂P) ≤
      2 * ((h : ℝ) * X.σ ^ 2) := by
  let Z : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hvar := avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
    X hν τ hτ T hbounded h
  have hNonneg : 0 ≤ (h : ℝ) * X.σ ^ 2 := by positivity
  exact avram_agentB_gaussian_centered_square_abs_moment_le_twice_variance
    P Z ((h : ℝ) * X.σ ^ 2) hNonneg hInt hvar
