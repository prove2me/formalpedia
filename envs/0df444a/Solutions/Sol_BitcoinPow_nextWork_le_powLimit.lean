-- Prove2me | solution 1 for BitcoinPow.nextWork_le_powLimit
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:56.961326+00:00
-- url     : https://prove2.me/submissions/2384292b-a56f-4be9-8325-134c8b370c76

import Definitions.Def_BitcoinPow
import Theorems.Thm_BitcoinPow_getCompact_le

open BitcoinPow

private theorem powLimit_lt_width : powLimit < width := by
  unfold powLimit width
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pow_lt_pow_right (by decide) (by decide))

/-- The capped value never exceeds the proof-of-work limit. -/
private theorem cap_le (x : Nat) : (if powLimit < x then powLimit else x) ≤ powLimit := by
  split <;> omega

theorem solution (lastBits : BitVec 32) (lastTime firstTime : Int) :
    BitcoinPow.setCompact (BitcoinPow.calculateNextWork lastBits lastTime firstTime) ≤ BitcoinPow.powLimit := by
  unfold calculateNextWork
  simp only []
  have hcap := cap_le ((setCompact lastBits * (clampTimespan (lastTime - firstTime)).toNat % width) / targetTimespan)
  exact Nat.le_trans (BitcoinPow.getCompact_le _ (Nat.lt_of_le_of_lt hcap powLimit_lt_width)) hcap
