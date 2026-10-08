-- Prove2me | solution 1 for CongestionPoA.SymMax.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T14:48:33.447437+00:00
-- url     : https://prove2.me/submissions/bc49eeb1-b7b0-477e-9228-3a9448070947

import Mathlib

set_option autoImplicit false

theorem solution (α β : ℕ) :
    (β : ℝ) * ((α : ℝ) + 1) ≤ (1 / 3 : ℝ) * (α : ℝ) ^ 2 + (5 / 3 : ℝ) * (β : ℝ) ^ 2 := by
  rcases Nat.lt_or_ge β 2 with h | h
  · interval_cases β
    · simp only [Nat.cast_zero, zero_mul]
      positivity
    · have key : ((α : ℝ) - 1) * ((α : ℝ) - 2) ≥ 0 := by
        rcases Nat.lt_or_ge α 2 with h2 | h2
        · interval_cases α <;> norm_num
        · have h2' : (2 : ℝ) ≤ α := by exact_mod_cast h2
          nlinarith
      push_cast
      nlinarith
  · have hb : (2 : ℝ) ≤ β := by exact_mod_cast h
    nlinarith [sq_nonneg ((α : ℝ) - 3 / 2 * β), mul_nonneg (by linarith : (0:ℝ) ≤ β)
      (by linarith : (0:ℝ) ≤ 11 / 4 * β - 3)]
