-- Prove2me | solution 1 for BlockCycleRotation.avgCost_le_three_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:33:07.273633+00:00
-- url     : https://prove2.me/submissions/6a3ece9e-f1c1-4dd4-b69c-3d6a0fde8792

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Average
import Definitions.Def_BlockCycleRotation_Euclid
import Theorems.Thm_BlockCycleRotation_cost_le_three_mul
import Mathlib

open Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

/-- Whatever the shift, the shorter segment is at most half the array. -/
theorem two_mul_min_le {n k : ℕ} (h : k ≤ n) : 2 * min k (n - k) ≤ n := by omega

/-- **Worst case.**  For any shift, the algorithm uses at most `3 * n` moves. -/
theorem algCost_le_three_mul {n k : ℕ} (h : k ≤ n) : algCost n k ≤ 3 * n :=
  cost_le_three_mul (two_mul_min_le h)

end BlockCycleRotation

open BlockCycleRotation in
/-- **The average cost is at most `3 * n`.**

Theorem 13 refines this to `D * n + O(n^(1/2+ε))` with `D ≈ 1.85`; see
`theorem13` in `Theorem13.lean`. -/
theorem solution {n : ℕ} (hn : 0 < n) : avgCost n ≤ 3 * n:= by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [avgCost, div_le_iff₀ hn']
  calc ∑ k ∈ range n, (algCost n k : ℝ)
      ≤ ∑ _k ∈ range n, (3 * n : ℝ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkn : k ≤ n := le_of_lt (mem_range.1 hk)
        exact_mod_cast algCost_le_three_mul hkn
    _ = n * (3 * n) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ = 3 * n * n := by ring
