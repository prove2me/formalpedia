-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_finite_cell_budget_to_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:26:34.127243+00:00
-- url     : https://prove2.me/submissions/953528ac-ad0a-40e3-9481-50ad9dd866db

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal BigOperators

/-! Uniform domination of finite discounted record-cell sums passes to their countable tsum. -/
theorem solution (f : ℕ → ℝ≥0∞) (C : ℝ≥0∞)
    (hfinite : ∀ N, (∑ n ∈ Finset.range N, f n) ≤ C) :
    (∑' n, f n) ≤ C := by
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le hfinite
