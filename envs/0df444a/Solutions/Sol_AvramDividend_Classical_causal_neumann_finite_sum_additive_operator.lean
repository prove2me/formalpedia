-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_finite_sum_additive_operator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T13:56:09.611016+00:00
-- url     : https://prove2.me/submissions/197ac0e2-dd01-44d1-ac6c-3817c286b782

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A zero-preserving additive operator distributes over finite Neumann sums. -/
theorem solution
    (T : (ℝ → ℝ) → (ℝ → ℝ)) (Q : ℕ → ℝ → ℝ)
    (hzero : T 0 = 0)
    (hadd : ∀ f g : ℝ → ℝ, T (f + g) = T f + T g)
    (n : ℕ) :
    T (∑ i ∈ Finset.range (n + 1), Q i) =
      ∑ i ∈ Finset.range (n + 1), T (Q i) := by
  classical
  have hfinite (m : ℕ) :
      T (∑ i ∈ Finset.range m, Q i) =
        ∑ i ∈ Finset.range m, T (Q i) := by
    induction m with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty]
        exact hzero
    | succ m ih =>
        simp only [Finset.sum_range_succ]
        rw [hadd, ih]
  exact hfinite (n + 1)
