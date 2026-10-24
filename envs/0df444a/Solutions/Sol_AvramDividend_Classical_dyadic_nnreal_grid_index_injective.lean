-- Prove2me | solution 1 for AvramDividend.Classical.dyadic_nnreal_grid_index_injective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:10:40.863626+00:00
-- url     : https://prove2.me/submissions/8a1c0829-2afe-4f5f-8a20-7d1252c9da09

import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- Positive dyadic scaling preserves distinct natural grid indices. -/
theorem solution
    (n : ℕ) :
    Function.Injective
      (fun k : ℕ => (k : ℝ≥0) / (2 : ℝ≥0) ^ n) := by
  have hstrict : StrictMono
      (fun k : ℕ => (k : ℝ≥0) / (2 : ℝ≥0) ^ n) := by
    intro a b hab
    exact div_lt_div_of_pos_right (Nat.cast_lt.mpr hab) (by positivity)
  exact hstrict.injective
