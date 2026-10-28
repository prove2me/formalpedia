-- Prove2me | solution 1 for BitcoinSubsidy.subsidy_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:50.637186+00:00
-- url     : https://prove2.me/submissions/f715b30c-3dfd-4f5f-b218-63a0715a608f

import Definitions.Def_BitcoinSubsidy
import Theorems.Thm_BitcoinSubsidy_core_eq_spec

open BitcoinSubsidy

theorem solution (height : Nat) :
    coreSubsidy height = 0 ↔ zeroHeight ≤ height := by
  rw [BitcoinSubsidy.core_eq_spec]
  unfold specSubsidy zeroHeight
  rw [Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
  constructor
  · intro h
    have h33 : 33 ≤ height / halvingInterval := by
      rcases Nat.lt_or_ge (height / halvingInterval) 33 with hlt | hge
      · have hle : height / halvingInterval ≤ 32 := Nat.le_of_lt_succ hlt
        have h1 : 2 ^ (height / halvingInterval) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hle
        have h2 : (50 * COIN) < 2 ^ 32 := Nat.lt_of_lt_of_le h h1
        exact absurd h2 (by decide)
      · exact hge
    exact (Nat.le_div_iff_mul_le (by decide : 0 < halvingInterval)).1 h33
  · intro h
    have h33 : 33 ≤ height / halvingInterval :=
      (Nat.le_div_iff_mul_le (by decide : 0 < halvingInterval)).2 h
    calc 50 * COIN < 2 ^ 33 := by decide
      _ ≤ 2 ^ (height / halvingInterval) := Nat.pow_le_pow_right (by decide) h33
