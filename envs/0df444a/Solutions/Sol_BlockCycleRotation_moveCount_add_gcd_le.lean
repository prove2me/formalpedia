-- Prove2me | solution 1 for BlockCycleRotation.moveCount_add_gcd_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:14:08.188507+00:00
-- url     : https://prove2.me/submissions/7f977b0a-7a8f-4062-91a1-f18791f974ee

import Definitions.Def_BlockCycleRotation_Euclid
import Theorems.Thm_BlockCycleRotation_remSum_add_gcd_le
import Mathlib


namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

/-- For `2 * k ≤ n`, the remainder sum is at most `n - gcd n k`.

Stated additively to avoid truncated subtraction. -/
theorem remSum_add_gcd_le_self {n k : ℕ} (h : 2 * k ≤ n) :
    remSum n k + Nat.gcd n k ≤ n := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  -- Since `2 * k ≤ n`, the first quotient is at least `2`, so `2 * k + n % k ≤ n`.
  have hq : 2 ≤ n / k := (Nat.le_div_iff_mul_le hk).2 (by linarith)
  have : 2 * k + n % k ≤ n := by nlinarith [Nat.div_add_mod n k]
  exact le_trans (remSum_add_gcd_le k n) this

end BlockCycleRotation

open BlockCycleRotation in
/-- **Worst case, Theorem A.**  The block cycle algorithm uses at most
`3 * (n - gcd n k)` moves; in particular at most `3 * n`. -/
theorem solution {n k : ℕ} (h : 2 * k ≤ n) :
    moveCount n k + 3 * Nat.gcd n k ≤ 3 * n:= by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hk : k = 0 := by omega
    subst hn; subst hk; simp [moveCount]
  · have hg : Nat.gcd n k ≤ n := Nat.le_of_dvd hn (Nat.gcd_dvd_left n k)
    have := remSum_add_gcd_le_self h
    simp only [moveCount]
    omega
