-- Prove2me | solution 1 for CongestionPoA.SymSum.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T08:55:28.60104+00:00
-- url     : https://prove2.me/submissions/e1ee315b-66d2-4b58-8382-dc28eca253ed

import Mathlib

theorem solution (α β : ℕ) :
    (β : ℝ) * ((α : ℝ) + 1) ≤ (1 / 3 : ℝ) * (α : ℝ) ^ 2 + (5 / 3 : ℝ) * (β : ℝ) ^ 2 := by
  have key : 3 * β * (α + 1) ≤ α ^ 2 + 5 * β ^ 2 := by
    rcases Nat.lt_or_ge β 2 with hb | hb
    · interval_cases β
      · simp
      · rcases Nat.lt_or_ge α 3 with ha | ha
        · interval_cases α <;> norm_num
        · nlinarith
    · have h1 : (0 : ℤ) ≤ (2 * (α : ℤ) - 3 * β) ^ 2 := sq_nonneg _
      have h2 : (0 : ℤ) ≤ (β : ℤ) * (11 * β - 12) := by
        apply mul_nonneg <;> omega
      zify
      nlinarith
  have : ((3 * β * (α + 1) : ℕ) : ℝ) ≤ ((α ^ 2 + 5 * β ^ 2 : ℕ) : ℝ) := by exact_mod_cast key
  push_cast at this
  linarith
