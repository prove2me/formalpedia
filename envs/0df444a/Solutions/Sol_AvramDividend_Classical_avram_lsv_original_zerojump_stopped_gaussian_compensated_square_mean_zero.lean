-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_zerojump_stopped_gaussian_compensated_square_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:57:12.835802+00:00
-- url     : https://prove2.me/submissions/da5e844c-fb31-4b7f-ab2a-921d5be037cf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopped_martingale_expectation

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/-
The original zero-jump Lévy compensated square, stopped at a genuine
bounded countable-range clock. Uses accepted Lean-LSV optional expectation
(CC BY 4.0, commit a5f604de2e1ae431de4cbecde23e5694a12ba719).
True martingale and exact Gaussian moments are original Avram proved inputs.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτle : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    let Q : ℝ≥0 → Ω → ℝ := fun t ω =>
      (X.X t ω - (t : ℝ) * X.c)^2 - (t : ℝ) * X.σ^2
    Integrable (stoppedValue Q τ) P ∧
      (∫ ω, stoppedValue Q τ ω ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Q : ℝ≥0 → Ω → ℝ := fun t ω =>
    (X.X t ω - (t : ℝ) * X.c)^2 - (t : ℝ) * X.σ^2
  change Integrable (stoppedValue Q τ) P ∧
    (∫ ω, stoppedValue Q τ ω ∂P) = 0
  have hQ : Martingale Q 𝓕.rightCont P :=
    avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
      X hν
  obtain ⟨hi, he⟩ :=
    avram_lsv_finite_grid_stopped_martingale_expectation
      P 𝓕.rightCont Q hQ T τ hτ hτle hτcount
  refine ⟨hi, he.trans ?_⟩
  have hm :=
    avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
      X hν T
  change (∫ ω, (X.X T ω - (T : ℝ) * X.c)^2 -
    (T : ℝ) * X.σ^2 ∂P) = 0
  rw [integral_sub hm.1 (integrable_const _), hm.2]
  simp

