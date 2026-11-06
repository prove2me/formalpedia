-- Prove2me | solution 2 for AvramDividend.Classical.avram_bv_env3_turn25_original_stopped_martingale_source_plus_negative_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:15:10.537292+00:00
-- url     : https://prove2.me/submissions/cbd1b05c-eaaa-4afb-a379-bfe7ff9505a1

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn22_original_martingale_physical_grid_increment_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn24_original_stopping_clock_signed_finite_grid_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Apply the true stopped-grid signed budget to chronological martingale increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : ℝ≥0 → Ω → ℝ)
    (hMart : Martingale Y 𝓕.rightCont P)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (B : ℕ → Ω → ℝ)
    (hBI : ∀ i, Integrable (B i) P)
    (hDrift : ∀ i ω, B i ω ≤ 0) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if (u i : WithTop ℝ≥0) < τ ω then
          (Y (u (i + 1)) ω - Y (u i) ω) + B i ω else 0) P ∧
    (∫ ω, ∑ i ∈ Finset.range m,
      (if (u i : WithTop ℝ≥0) < τ ω then
        (Y (u (i + 1)) ω - Y (u i) ω) + B i ω else 0) ∂P) ≤ 0 := by
  let M : ℕ → Ω → ℝ := fun i ω => Y (u (i + 1)) ω - Y (u i) ω
  have hMI : ∀ i, Integrable (M i) P := by
    intro i
    exact (hMart.integrable (u (i + 1))).sub (hMart.integrable (u i))
  have hCondZero : ∀ i, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont (u i)) P (M i) ω = 0 := by
    intro i
    exact avram_bv_env3_turn22_original_martingale_physical_grid_increment_condexp_zero
      X Y hMart u hu i
  exact avram_bv_env3_turn24_original_stopping_clock_signed_finite_grid_budget
    X τ hStop u m M B hMI hBI hCondZero hDrift
