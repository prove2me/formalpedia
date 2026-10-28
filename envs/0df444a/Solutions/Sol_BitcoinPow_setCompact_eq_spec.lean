-- Prove2me | solution 1 for BitcoinPow.setCompact_eq_spec
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:53.499657+00:00
-- url     : https://prove2.me/submissions/22af66a3-7eb7-41ee-a9c9-3152df75ff86

import Definitions.Def_BitcoinPow
import Theorems.Thm_BitcoinPow_overflow_iff

open BitcoinPow

private theorem pow256_eq (k : Nat) : (256 : Nat) ^ k = 2 ^ (8 * k) := by
  rw [Nat.pow_mul]

theorem solution (c : BitVec 32) (h : BitcoinPow.compactOverflow c = false) :
    BitcoinPow.setCompact c = BitcoinPow.specTarget c := by
  have hlt : specTarget c < width := by
    rcases Nat.lt_or_ge (specTarget c) width with hlt | hge
    · exact hlt
    · have := (BitcoinPow.overflow_iff c).2 hge; rw [h] at this; exact absurd this (by decide)
  unfold setCompact specTarget at *
  simp only [] at hlt ⊢
  by_cases h3 : compactSize c ≤ 3
  · simp only [if_pos h3, Nat.shiftRight_eq_div_pow, ← pow256_eq]
  · simp only [if_neg h3] at hlt ⊢
    rw [Nat.shiftLeft_eq, ← pow256_eq]
    exact Nat.mod_eq_of_lt hlt
