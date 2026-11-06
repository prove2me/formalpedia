-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_contact_left_endpoint_approach_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:01:40.932162+00:00
-- url     : https://prove2.me/submissions/418189d4-df3c-4ac9-af02-cb5b8ea6ee2b

import Mathlib.Data.NNReal.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Defs.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_contact_left_endpoint_real_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
open scoped NNReal

/-- The exact original physical tail endpoints increase strictly below a positive stop. -/
theorem solution
    (τ T : ℝ≥0) (hτ : 0 < τ) (hT : 0 < T) :
    let a : ℕ → ℝ := fun n =>
      ((τ - T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ)
    Monotone a ∧ Tendsto a atTop (𝓝 (τ : ℝ)) ∧
      (∀ n, a n < (τ : ℝ)) := by
  let a : ℕ → ℝ := fun n =>
    ((τ - T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ)
  change Monotone a ∧ Tendsto a atTop (𝓝 (τ : ℝ)) ∧
    (∀ n, a n < (τ : ℝ))
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have hDen : ((i + 1 : ℕ) : ℝ≥0) ≤ ((j + 1 : ℕ) : ℝ≥0) := by
      exact_mod_cast Nat.add_le_add_right hij 1
    have hDel : T / ((j + 1 : ℕ) : ℝ≥0) ≤
        T / ((i + 1 : ℕ) : ℝ≥0) := by
      gcongr
    have hFloor :
        τ - T / ((i + 1 : ℕ) : ℝ≥0) ≤
        τ - T / ((j + 1 : ℕ) : ℝ≥0) :=
      tsub_le_tsub_left hDel τ
    have hFloorReal :
        ((τ - T / ((i + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) ≤
        ((τ - T / ((j + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := by
      exact_mod_cast hFloor
    simpa only [a, Nat.cast_add, Nat.cast_one] using hFloorReal
  · simpa only [a] using
      (avram_p3_grid4_contact_left_endpoint_real_tendsto τ T)
  · intro n
    have hDen : (0 : ℝ≥0) < (n : ℝ≥0) + 1 := by positivity
    have hWidth : (0 : ℝ≥0) < T / ((n : ℝ≥0) + 1) :=
      div_pos hT hDen
    have hLess : τ - T / ((n : ℝ≥0) + 1) < τ :=
      tsub_lt_self hτ hWidth
    change ((τ - T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) < (τ : ℝ)
    exact_mod_cast hLess
