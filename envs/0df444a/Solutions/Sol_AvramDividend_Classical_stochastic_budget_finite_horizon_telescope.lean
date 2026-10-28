-- Prove2me | solution 1 for AvramDividend.Classical.stochastic_budget_finite_horizon_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:59:11.346738+00:00
-- url     : https://prove2.me/submissions/79c09720-3edd-4384-b18f-96cf270d7abb

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal BigOperators

theorem solution
    (v r : ℕ → ℝ≥0∞)
    (hstep : ∀ k, v (k + 1) + r k ≤ v k)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, r k) + v n ≤ v 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (∑ k ∈ Finset.range (n + 1), r k) + v (n + 1) =
            (∑ k ∈ Finset.range n, r k) + (v (n + 1) + r n) := by
              rw [Finset.sum_range_succ]
              ac_rfl
        _ ≤ (∑ k ∈ Finset.range n, r k) + v n :=
          by
            convert add_le_add_left (hstep n)
              (∑ k ∈ Finset.range n, r k) using 1 <;> ac_rfl
        _ ≤ v 0 := ih
