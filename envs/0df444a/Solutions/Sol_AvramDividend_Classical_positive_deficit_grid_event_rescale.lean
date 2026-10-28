-- Prove2me | solution 1 for AvramDividend.Classical.positive_deficit_grid_event_rescale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T14:47:50.839984+00:00
-- url     : https://prove2.me/submissions/19b22ec1-4f3c-4749-b64c-adf7116b048c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Order.Ring.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A positive number of mesh cells rescales the deficit event equivalently. -/
theorem solution
    {Ω : Type*} (D : Ω → ℝ) (N : ℕ) (hN : 0 < N) (b : ℝ) :
    {ω : Ω | 0 < D ω ∧ D ω ≤ b} =
      {ω : Ω | 0 < D ω ∧ (N : ℝ) * D ω ≤ (N : ℝ) * b} := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hPos, hSmall⟩
    exact ⟨hPos, mul_le_mul_of_nonneg_left hSmall (le_of_lt hNreal)⟩
  · rintro ⟨hPos, hSmall⟩
    exact ⟨hPos, le_of_mul_le_mul_left hSmall hNreal⟩
