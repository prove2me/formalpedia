-- Prove2me | solution 1 for BitcoinSubsidy.subsidy_halving
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:50.097695+00:00
-- url     : https://prove2.me/submissions/82963d24-00cd-4bbb-90b2-15c5ead57c59

import Definitions.Def_BitcoinSubsidy
import Theorems.Thm_BitcoinSubsidy_core_eq_spec

open BitcoinSubsidy

theorem solution (height : Nat) :
    coreSubsidy (height + halvingInterval) = coreSubsidy height / 2 := by
  rw [BitcoinSubsidy.core_eq_spec, BitcoinSubsidy.core_eq_spec]
  unfold specSubsidy
  rw [Nat.add_div_right _ (by decide : 0 < halvingInterval), Nat.pow_succ, Nat.div_div_eq_div_mul]
