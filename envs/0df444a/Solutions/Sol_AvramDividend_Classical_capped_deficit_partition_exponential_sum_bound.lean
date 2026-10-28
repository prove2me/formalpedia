-- Prove2me | solution 1 for AvramDividend.Classical.capped_deficit_partition_exponential_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:15:27.61522+00:00
-- url     : https://prove2.me/submissions/eed4e727-2c51-42f0-a46c-9d32e4392926

import Theorems.Thm_AvramDividend_Classical_nonnegative_truncated_le_exp_gap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset
open scoped BigOperators

theorem solution
    (D : ℕ → ℝ) (N : ℕ) (a : ℝ) (ha : 0 < a)
    (hNonneg : ∀ k : ℕ, k < N → 0 ≤ D (k + 1) - D k)
    (hCap : ∀ k : ℕ, k < N → D (k + 1) - D k ≤ a) :
    D N - D 0 ≤
      4 * a * ∑ k ∈ Finset.range N,
        (1 - Real.exp (-((D (k + 1) - D k) / (2 * a)))) := by
  rw [← Finset.sum_range_sub (fun k => D k) N, Finset.mul_sum]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hk' := Finset.mem_range.1 hk
  exact AvramDividend.Classical.nonnegative_truncated_le_exp_gap a _ ha (hNonneg k hk') (hCap k hk')
