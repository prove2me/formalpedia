-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn12_original_clock_selected_random_grid_signed_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:58:04.484457+00:00
-- url     : https://prove2.me/submissions/2c81088d-e7d4-44d1-96a0-799ce50b135f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_stopping_grid_prefix_card_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_stopping_grid_prefix_count_adapted
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_double_stopped_condexp_random_mesh_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_random_mesh_stopped_HJB_signed_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- For the original Lévy process, the true stopped physical mesh count
is predictable, and its compensated source plus nonpositive HJB drift
has nonpositive expectation with no externally assumed grid-index selector. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (M B : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hBI : ∀ i, Integrable (B i) P)
    (hCondZero : ∀ i, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont (u i)) P (M i) ω = 0)
    (hDrift : ∀ i ω, B i ω ≤ 0) :
    let k : Ω → ℕ := fun ω =>
      ((Finset.range m).filter
        (fun j => (u j : WithTop ℝ≥0) < τ ω)).card
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω),
      if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω),
      (if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0) ∂P) ≤ 0 := by
  classical
  dsimp
  let k : Ω → ℕ := fun ω =>
    ((Finset.range m).filter
      (fun j => (u j : WithTop ℝ≥0) < τ ω)).card
  have hk := avram_bv_env3_turn12_original_stopping_grid_prefix_card_measurable
    X τ hStop u m
  have hka := avram_bv_env3_turn12_original_stopping_grid_prefix_count_adapted
    X τ hStop u hu m
  have hM := avram_bv_env3_turn12_original_double_stopped_condexp_random_mesh_mean_zero
    X τ hStop u m k hk.1 hk.2 hka M hMI hCondZero
  exact avram_bv_env3_turn12_original_random_mesh_stopped_HJB_signed_budget
    X τ hStop u m k hk.1 hk.2 M B hMI hBI hDrift hM.2
