-- Prove2me | solution 1 for AvramDividend.Classical.dyadic_ceiling_index_eq_iff_time_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:07:18.13137+00:00
-- url     : https://prove2.me/submissions/016d14b4-80f5-406f-84d3-914190536a47

import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- A positive dyadic ceiling index identifies exactly one half-open time cell. -/
theorem solution
    (t : ℝ≥0) (n k : ℕ) (hk : k ≠ 0) :
    Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) = k ↔
      ((k - 1 : ℕ) : ℝ) / (2 : ℝ) ^ n < (t : ℝ) ∧
      (t : ℝ) ≤ (k : ℝ) / (2 : ℝ) ^ n := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [Nat.ceil_eq_iff hk, div_lt_iff₀ hp, le_div_iff₀ hp]
