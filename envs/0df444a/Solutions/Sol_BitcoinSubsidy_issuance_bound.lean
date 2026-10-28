-- Prove2me | solution 1 for BitcoinSubsidy.issuance_bound
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:52.377715+00:00
-- url     : https://prove2.me/submissions/09d0a4b2-8a0f-41c4-ab54-e1c3688644de

import Definitions.Def_BitcoinSubsidy
import Theorems.Thm_BitcoinSubsidy_issuance_le_total

open BitcoinSubsidy

theorem solution (n : Nat) : issuedBelow n < MAX_MONEY := by
  calc issuedBelow n ≤ 2099999997690000 := BitcoinSubsidy.issuance_le_total n
    _ < MAX_MONEY := by decide
