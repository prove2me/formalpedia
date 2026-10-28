-- Prove2me | solution 1 for BitcoinPow.clamp_bounds
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:56.342781+00:00
-- url     : https://prove2.me/submissions/5cb5b2f1-fe54-43da-b9e6-468acaed80f1

import Definitions.Def_BitcoinPow

open BitcoinPow

theorem solution (actual : Int) :
    ((BitcoinPow.targetTimespan / 4 : Nat) : Int) ≤ BitcoinPow.clampTimespan actual ∧
    BitcoinPow.clampTimespan actual ≤ ((BitcoinPow.targetTimespan * 4 : Nat) : Int) := by
  unfold clampTimespan targetTimespan
  simp only []
  by_cases h1 : actual < ((14 * 24 * 60 * 60 / 4 : Nat) : Int)
  · rw [if_pos h1]; constructor <;> omega
  · rw [if_neg h1]
    by_cases h2 : ((14 * 24 * 60 * 60 * 4 : Nat) : Int) < actual
    · rw [if_pos h2]; constructor <;> omega
    · rw [if_neg h2]; constructor <;> omega
