-- Prove2me | solution 1 for BitcoinPow.nextWork_permitted
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:58.170159+00:00
-- url     : https://prove2.me/submissions/1d7ddbec-ebe3-4b1f-bca7-1e3e77962ec1

import Definitions.Def_BitcoinPow
import Theorems.Thm_BitcoinPow_clamp_bounds
import Theorems.Thm_BitcoinPow_round_mono

open BitcoinPow

private theorem powLimit_lt_width : powLimit < width := by
  unfold powLimit width
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pow_lt_pow_right (by decide) (by decide))

/-- The capped value never exceeds the proof-of-work limit. -/
private theorem cap_le (x : Nat) : (if powLimit < x then powLimit else x) ≤ powLimit := by
  split <;> omega

private theorem cap_mono (x y : Nat) (h : x ≤ y) :
    (if powLimit < x then powLimit else x) ≤ (if powLimit < y then powLimit else y) := by
  split <;> split <;> omega

theorem solution (height : Nat) (lastBits : BitVec 32) (lastTime firstTime : Int)
    (hh : height % BitcoinPow.difficultyAdjustmentInterval = 0)
    (hold : BitcoinPow.setCompact lastBits ≤ BitcoinPow.powLimit) :
    BitcoinPow.permittedTransition height lastBits
      (BitcoinPow.calculateNextWork lastBits lastTime firstTime) = true := by
  unfold permittedTransition calculateNextWork
  rw [if_pos hh]
  simp only []
  -- name the ingredients
  have hclamp := BitcoinPow.clamp_bounds (lastTime - firstTime)
  generalize hts : (clampTimespan (lastTime - firstTime)).toNat = ts at *
  have hts_lo : targetTimespan / 4 ≤ ts := by omega
  have hts_hi : ts ≤ targetTimespan * 4 := by omega
  generalize hold' : setCompact lastBits = old at *
  -- no 256-bit wrap-around in any of the three products
  have hT : targetTimespan * 4 < 2 ^ 32 := by decide
  have hprod : ∀ t, t ≤ targetTimespan * 4 → old * t < width := by
    intro t ht
    calc old * t ≤ powLimit * (targetTimespan * 4) := Nat.mul_le_mul hold ht
      _ < 2 ^ 224 * 2 ^ 32 := Nat.mul_lt_mul_of_lt_of_le (by unfold powLimit; omega) (Nat.le_of_lt hT) (Nat.two_pow_pos _)
      _ = width := by unfold width; rw [← Nat.pow_add]
  have hq : targetTimespan / 4 ≤ targetTimespan * 4 := by unfold targetTimespan; omega
  have hp1 := hprod ts hts_hi
  have hp2 := hprod (targetTimespan * 4) (Nat.le_refl _)
  have hp3 := hprod (targetTimespan / 4) hq
  simp only [Nat.mod_eq_of_lt hp1, Nat.mod_eq_of_lt hp2, Nat.mod_eq_of_lt hp3]
  -- the three capped quotients, ordered
  have h1 : old * (targetTimespan / 4) / targetTimespan ≤ old * ts / targetTimespan :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ hts_lo)
  have h2 : old * ts / targetTimespan ≤ old * (targetTimespan * 4) / targetTimespan :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ hts_hi)
  have hmin := cap_mono _ _ h1
  have hmax := cap_mono _ _ h2
  have hobs_lt : (if powLimit < old * ts / targetTimespan then powLimit else old * ts / targetTimespan) < width :=
    Nat.lt_of_le_of_lt (cap_le _) powLimit_lt_width
  have hmax_lt : (if powLimit < old * (targetTimespan * 4) / targetTimespan then powLimit
      else old * (targetTimespan * 4) / targetTimespan) < width :=
    Nat.lt_of_le_of_lt (cap_le _) powLimit_lt_width
  have hA := BitcoinPow.round_mono _ _ hmax hmax_lt
  have hB := BitcoinPow.round_mono _ _ hmin hobs_lt
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt, gt_iff_lt]
  exact ⟨hA, hB⟩
