-- Prove2me | solution 2 for BitcoinDifficulty.target_after_upper
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:16:12.551571+00:00
-- url     : https://prove2.me/submissions/ab7a8a12-4bfa-4dea-a101-caab32916fa7

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

/-- Over `m` periods the encoded target grows by at most `4^m`, whatever the timestamps. -/
theorem solution (bits : BitVec 32) (hb : BitcoinPow.setCompact bits ≤ BitcoinPow.powLimit) :
    ∀ (periods : List (Int × Int)),
    BitcoinPow.setCompact (BitcoinDifficulty.targetAfter bits periods) ≤ 4 ^ periods.length * BitcoinPow.setCompact bits := by
  intro periods
  induction periods generalizing bits with
  | nil => simp [targetAfter]
  | cons p rest ih =>
    obtain ⟨lt, ft⟩ := p
    simp only [targetAfter, List.length_cons]
    have hb' := BitcoinPow.nextWork_le_powLimit bits lt ft
    have h1 := ih (calculateNextWork bits lt ft) hb'
    have h2 := BitcoinDifficulty.encoded_target_upper bits hb lt ft
    calc setCompact (targetAfter (calculateNextWork bits lt ft) rest)
        ≤ 4 ^ rest.length * setCompact (calculateNextWork bits lt ft) := h1
      _ ≤ 4 ^ rest.length * (4 * setCompact bits) := Nat.mul_le_mul_left _ h2
      _ = 4 ^ (rest.length + 1) * setCompact bits := by rw [Nat.pow_succ, Nat.mul_assoc]
