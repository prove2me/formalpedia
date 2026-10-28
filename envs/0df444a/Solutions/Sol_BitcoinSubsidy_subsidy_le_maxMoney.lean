-- Prove2me | solution 1 for BitcoinSubsidy.subsidy_le_maxMoney
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:48.892916+00:00
-- url     : https://prove2.me/submissions/809b7b45-656a-4811-8144-e35ca2160a7c

import Definitions.Def_BitcoinSubsidy
import Theorems.Thm_BitcoinSubsidy_core_eq_spec

open BitcoinSubsidy

theorem solution (height : Nat) : coreSubsidy height ≤ MAX_MONEY := by
  rw [BitcoinSubsidy.core_eq_spec]
  unfold specSubsidy
  calc (50 * COIN) / 2 ^ (height / halvingInterval) ≤ 50 * COIN := Nat.div_le_self _ _
    _ ≤ MAX_MONEY := by decide
