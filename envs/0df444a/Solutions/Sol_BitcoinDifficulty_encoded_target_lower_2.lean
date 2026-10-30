-- Prove2me | solution 2 for BitcoinDifficulty.encoded_target_lower
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:15:43.302243+00:00
-- url     : https://prove2.me/submissions/d36877cf-b1fe-4c57-81b3-068afa4961dd

import Definitions.Def_BitcoinDifficulty
import Theorems.Thm_BitcoinPow_clamp_bounds
import Theorems.Thm_BitcoinPow_getCompact_le
import Theorems.Thm_BitcoinPow_nextWork_le_powLimit
import Theorems.Thm_BitcoinPow_round_mono
import Theorems.Thm_BitcoinDifficulty_raw_target_bounds

open BitcoinDifficulty BitcoinPow

private theorem clamp_nat_bounds (actual : Int) :
    302400 ≤ (clampTimespan actual).toNat ∧ (clampTimespan actual).toNat ≤ 4838400 := by
  have h := BitcoinPow.clamp_bounds actual
  simp only [targetTimespan] at h
  omega

private theorem calculateNextWork_eq (bits : BitVec 32) (lastTime firstTime : Int) :
    calculateNextWork bits lastTime firstTime = getCompact (rawNextTarget (setCompact bits) lastTime firstTime) := rfl

private theorem raw_lt_width (t : Nat) (ht : t ≤ powLimit) (lastTime firstTime : Int) :
    rawNextTarget t lastTime firstTime < width := by
  have h := (BitcoinDifficulty.raw_target_bounds t ht lastTime firstTime).1
  simp only [powLimit, width] at ht ⊢
  omega

/-- **The encoded target drops by at most a factor of four per period**, up to the compact
rounding: the new target is at least the encoding of a quarter of the old one. -/
theorem solution (bits : BitVec 32) (hb : BitcoinPow.setCompact bits ≤ BitcoinPow.powLimit)
    (lastTime firstTime : Int) :
    BitcoinPow.setCompact (BitcoinPow.getCompact (BitcoinPow.setCompact bits / 4)) ≤
      BitcoinPow.setCompact (BitcoinPow.calculateNextWork bits lastTime firstTime) := by
  rw [calculateNextWork_eq]
  have hw := raw_lt_width _ hb lastTime firstTime
  rcases (BitcoinDifficulty.raw_target_bounds _ hb lastTime firstTime).2 with hcap | hlow
  · rw [hcap]
    apply BitcoinPow.round_mono
    · have := Nat.div_le_self (setCompact bits) 4; omega
    · simp only [powLimit, width]; decide
  · exact BitcoinPow.round_mono _ _ hlow hw
