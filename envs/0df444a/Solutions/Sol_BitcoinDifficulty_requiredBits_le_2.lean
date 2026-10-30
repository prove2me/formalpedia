-- Prove2me | solution 2 for BitcoinDifficulty.requiredBits_le
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:16:13.483236+00:00
-- url     : https://prove2.me/submissions/27a0bb6f-4fe6-4500-beac-e99b48442d30

import Definitions.Def_BitcoinDifficulty
import Theorems.Thm_BitcoinPow_clamp_bounds
import Theorems.Thm_BitcoinPow_getCompact_le
import Theorems.Thm_BitcoinPow_nextWork_le_powLimit
import Theorems.Thm_BitcoinPow_round_mono
import Theorems.Thm_BitcoinDifficulty_encoded_target_upper
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

/-- **Timewarp bound.** On a chain whose tip is at a retarget boundary with a valid target, the
required target of the next block is at most four times the tip's target, whatever the block
timestamps were (`ChainState.requiredBits` of the block mission). -/
theorem solution (S : BitcoinBlockV2.ChainState)
    (hb : BitcoinPow.setCompact (BitVec.ofNat 32 S.tip.bits) ≤ BitcoinPow.powLimit) :
    BitcoinPow.setCompact S.requiredBits ≤ 4 * BitcoinPow.setCompact (BitVec.ofNat 32 S.tip.bits) := by
  simp only [BitcoinBlockV2.ChainState.requiredBits, nextWorkRequired]
  split
  · omega
  · exact BitcoinDifficulty.encoded_target_upper _ hb _ _
