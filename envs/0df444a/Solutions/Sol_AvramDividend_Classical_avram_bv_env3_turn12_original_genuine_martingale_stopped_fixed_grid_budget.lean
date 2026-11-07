-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn12_original_genuine_martingale_stopped_fixed_grid_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:53:44.180027+00:00
-- url     : https://prove2.me/submissions/71be60d4-39db-4f56-8997-41760d3f1710

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn24_original_stopping_clock_signed_finite_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn22_original_martingale_physical_grid_increment_condexp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original martingale increments replace abstract source conditional-zero
assumptions in the genuine original stopping-clock physical-grid budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (Y : ℝ≥0 → Ω → ℝ) (hMart : Martingale Y 𝓕.rightCont P)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (B : ℕ → Ω → ℝ) (hBI : ∀ i, Integrable (B i) P)
    (hDrift : ∀ i ω, B i ω ≤ 0) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if (u i : WithTop ℝ≥0) < τ ω then
          (Y (u (i + 1)) ω - Y (u i) ω) + B i ω else 0) P ∧
    (∫ ω, ∑ i ∈ Finset.range m,
        (if (u i : WithTop ℝ≥0) < τ ω then
          (Y (u (i + 1)) ω - Y (u i) ω) + B i ω else 0)
      ∂P) ≤ 0 := by
  have hMI (i : ℕ) :
      Integrable (fun ω => Y (u (i + 1)) ω - Y (u i) ω) P :=
    (hMart.integrable (u (i + 1))).sub (hMart.integrable (u i))
  have hCondZero (i : ℕ) :
      P[(fun ω => Y (u (i + 1)) ω - Y (u i) ω) | 𝓕.rightCont (u i)]
        =ᵐ[P] (fun _ => (0 : ℝ)) :=
    avram_bv_env3_turn22_original_martingale_physical_grid_increment_condexp_zero
      X Y hMart u hu i
  exact avram_bv_env3_turn24_original_stopping_clock_signed_finite_grid_budget
    X τ hStop u m
    (fun i ω => Y (u (i + 1)) ω - Y (u i) ω)
    B hMI hBI hCondZero hDrift
