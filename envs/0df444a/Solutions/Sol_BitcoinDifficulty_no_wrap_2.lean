-- Prove2me | solution 2 for BitcoinDifficulty.no_wrap
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:14:43.293734+00:00
-- url     : https://prove2.me/submissions/ed636182-cde5-4c6e-8077-3c14681a4e3a

import Definitions.Def_BitcoinDifficulty
import Theorems.Thm_BitcoinPow_clamp_bounds
import Theorems.Thm_BitcoinPow_getCompact_le
import Theorems.Thm_BitcoinPow_nextWork_le_powLimit
import Theorems.Thm_BitcoinPow_round_mono

open BitcoinDifficulty BitcoinPow

private theorem clamp_nat_bounds (actual : Int) :
    302400 ≤ (clampTimespan actual).toNat ∧ (clampTimespan actual).toNat ≤ 4838400 := by
  have h := BitcoinPow.clamp_bounds actual
  simp only [targetTimespan] at h
  omega

/-- The product of a valid target and the clamped timespan never wraps around `2^256`. -/
theorem solution (t : Nat) (ht : t ≤ BitcoinPow.powLimit) (ts : Nat) (hts : ts ≤ 4838400) :
    t * ts < BitcoinPow.width := by
  simp only [powLimit] at ht
  simp only [width]
  have h1 : t * ts ≤ (2 ^ 224 - 1) * 4838400 := Nat.mul_le_mul ht hts
  have h2 : (2 ^ 224 - 1) * 4838400 < 2 ^ 256 := by decide
  omega
