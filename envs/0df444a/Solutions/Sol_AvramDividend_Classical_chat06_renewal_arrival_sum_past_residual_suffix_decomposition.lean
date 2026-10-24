-- Prove2me | solution 1 for AvramDividend.Classical.chat06_renewal_arrival_sum_past_residual_suffix_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T13:25:14.361526+00:00
-- url     : https://prove2.me/submissions/0c0db37a-cba8-415c-aa84-e452ea85ee86

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Split a finite arrival-time sum into prefix, current wait, and suffix. -/
theorem solution (τ : ℕ → ℝ) (n k : ℕ) :
    (∑ i ∈ Finset.range (n + k + 1), τ i) =
      ((∑ i ∈ Finset.range n, τ i) + τ n) +
        ∑ j ∈ Finset.range k, τ (n + 1 + j) := by
  have hindex : n + k + 1 = (n + 1) + k := by omega
  rw [hindex, Finset.sum_range_add, Finset.sum_range_succ]
