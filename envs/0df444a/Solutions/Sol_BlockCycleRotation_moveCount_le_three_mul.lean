-- Prove2me | solution 1 for BlockCycleRotation.moveCount_le_three_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:14:08.131076+00:00
-- url     : https://prove2.me/submissions/9d187735-fe3d-42fe-ad7d-bfc5bf310991

import Definitions.Def_BlockCycleRotation_Euclid
import Theorems.Thm_BlockCycleRotation_moveCount_add_gcd_le
import Mathlib


namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- The block cycle algorithm never uses more than `3 * n` moves. -/
theorem solution {n k : ℕ} (h : 2 * k ≤ n) : moveCount n k ≤ 3 * n:= by
  have := moveCount_add_gcd_le h
  omega
