-- Prove2me | solution 1 for Formalism.QuantumDeterminants.prod_range_sub_cast_eq_factorial
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T10:37:06.050708+00:00
-- url     : https://prove2.me/submissions/8366909b-9c0e-4280-9ce0-354683c7c890

import Mathlib

open Finset Nat BigOperators

theorem solution (b : ℕ) : ∏ j ∈ range b, ((b : ℝ) - (j : ℝ)) = (b.factorial : ℝ) := by
  have hcast : ∏ j ∈ range b, ((b : ℝ) - j) = ((∏ j ∈ range b, (b - j) : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    apply prod_congr rfl
    intro j hj
    exact (Nat.cast_sub (le_of_lt (mem_range.mp hj))).symm
  rw [hcast]
  norm_cast
  rw [← prod_range_reflect]
  have : ∏ j ∈ range b, (b - (b - 1 - j)) = ∏ j ∈ range b, (j + 1) := by
    apply prod_congr rfl
    intro j hj
    have hjb : j < b := mem_range.mp hj
    omega
  rw [this, ← factorial_eq_prod_range_add_one]
