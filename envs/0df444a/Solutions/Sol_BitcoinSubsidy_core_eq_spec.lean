-- Prove2me | solution 1 for BitcoinSubsidy.core_eq_spec
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:48.184266+00:00
-- url     : https://prove2.me/submissions/94ed1c46-18e0-43e3-81ab-51383a81fa12

import Definitions.Def_BitcoinSubsidy

open BitcoinSubsidy

theorem solution (height : Nat) : coreSubsidy height = specSubsidy height := by
  unfold coreSubsidy specSubsidy
  simp only []
  split
  · rename_i h
    symm
    apply Nat.div_eq_of_lt
    calc 50 * COIN < 2 ^ 64 := by decide
      _ ≤ 2 ^ (height / halvingInterval) := Nat.pow_le_pow_right (by decide) h
  · exact Nat.shiftRight_eq_div_pow _ _
