-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn12_original_clock_selected_genuine_martingale_signed_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:58:54.376857+00:00
-- url     : https://prove2.me/submissions/28b07458-cee3-4779-a7fa-b54e27acfc5a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_stopping_grid_prefix_card_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_stopping_grid_prefix_count_adapted
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn29_original_source_predictable_bounded_prefix_signed_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuinely original martingale increments have nonpositive stopped signed
source budget for the exact clock-selected finite grid prefix. -/
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
    let k : Ω → ℕ := fun ω =>
      ((Finset.range m).filter
        (fun j => (u j : WithTop ℝ≥0) < τ ω)).card
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω),
      ((Y (u (i + 1)) ω - Y (u i) ω) + B i ω)) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω),
      ((Y (u (i + 1)) ω - Y (u i) ω) + B i ω) ∂P) ≤ 0 := by
  dsimp
  let k : Ω → ℕ := fun ω =>
    ((Finset.range m).filter
      (fun j => (u j : WithTop ℝ≥0) < τ ω)).card
  have hk := avram_bv_env3_turn12_original_stopping_grid_prefix_card_measurable
    X τ hStop u m
  have hp := avram_bv_env3_turn12_original_stopping_grid_prefix_count_adapted
    X τ hStop u hu m
  exact avram_bv_env3_turn29_original_source_predictable_bounded_prefix_signed_budget
    X Y hMart u hu m k hk.1 hk.2 hp B hBI hDrift
