-- Prove2me | solution 1 for AvramDividend.Classical.chat04_countable_shifted_two_sided_survival_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:49:15.367002+00:00
-- url     : https://prove2.me/submissions/634eef6b-b772-458a-9251-c269bc061511

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_upper_survival_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Survival inside both barriers at countably many future times is Borel. -/
theorem solution
    (τ : ℕ → ℝ≥0) (T : ℝ≥0) (a : ℝ) :
    MeasurableSet
      {z : ℝ × (ℝ≥0 → ℝ) |
        ∀ j : ℕ, τ j ≤ T →
          0 ≤ z.1 + z.2 (τ j) ∧ z.1 + z.2 (τ j) ≤ a} := by
  have hLower :=
    chat04_countable_shifted_future_reserve_survival_measurable τ T
  have hUpper :=
    chat04_countable_shifted_future_reserve_upper_survival_measurable τ T a
  have hEq :
      {z : ℝ × (ℝ≥0 → ℝ) |
        ∀ j : ℕ, τ j ≤ T →
          0 ≤ z.1 + z.2 (τ j) ∧ z.1 + z.2 (τ j) ≤ a} =
      {z : ℝ × (ℝ≥0 → ℝ) |
        ∀ j : ℕ, τ j ≤ T → 0 ≤ z.1 + z.2 (τ j)} ∩
      {z : ℝ × (ℝ≥0 → ℝ) |
        ∀ j : ℕ, τ j ≤ T → z.1 + z.2 (τ j) ≤ a} := by
    ext z
    constructor
    · intro h
      exact ⟨(fun j hj => (h j hj).1),
        (fun j hj => (h j hj).2)⟩
    · rintro ⟨hlo, hup⟩ j hj
      exact ⟨hlo j hj, hup j hj⟩
  rw [hEq]
  exact hLower.inter hUpper
