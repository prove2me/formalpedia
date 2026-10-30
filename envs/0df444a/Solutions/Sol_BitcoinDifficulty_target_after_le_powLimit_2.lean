-- Prove2me | solution 2 for BitcoinDifficulty.target_after_le_powLimit
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:15:43.794892+00:00
-- url     : https://prove2.me/submissions/4c6b32b8-21cb-4bc0-9764-63a652e8893f

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

/-- The target never exceeds `powLimit` after any number of periods. -/
theorem solution (bits : BitVec 32) (hb : BitcoinPow.setCompact bits ≤ BitcoinPow.powLimit) :
    ∀ (periods : List (Int × Int)), BitcoinPow.setCompact (BitcoinDifficulty.targetAfter bits periods) ≤ BitcoinPow.powLimit := by
  intro periods
  induction periods generalizing bits with
  | nil => simpa [targetAfter] using hb
  | cons p rest ih =>
    obtain ⟨lt, ft⟩ := p
    simp only [targetAfter]
    exact ih _ (BitcoinPow.nextWork_le_powLimit bits lt ft)
