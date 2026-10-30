-- Prove2me | solution 1 for BitcoinDifficulty.raw_target_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:59:53.097986+00:00
-- url     : https://prove2.me/submissions/7c624368-b263-46e3-b292-3df3bfe8a387

import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow
theorem solution (t : Nat) (ht : t ≤ BitcoinPow.powLimit) (lastTime firstTime : Int) :
    BitcoinDifficulty.rawNextTarget t lastTime firstTime ≤ 4 * t ∧
    (BitcoinDifficulty.rawNextTarget t lastTime firstTime = BitcoinPow.powLimit ∨
      t / 4 ≤ BitcoinDifficulty.rawNextTarget t lastTime firstTime) := by
  have hc : (302400 : Int) ≤ clampTimespan (lastTime - firstTime) ∧
      clampTimespan (lastTime - firstTime) ≤ 4838400 := by
    have e1 : ((14 * 24 * 60 * 60 / 4 : Nat) : Int) = 302400 := by decide
    have e2 : ((14 * 24 * 60 * 60 * 4 : Nat) : Int) = 4838400 := by decide
    simp only [clampTimespan, targetTimespan, e1, e2]
    by_cases ha : lastTime - firstTime < 302400
    · simp only [ha, if_true]; omega
    · by_cases hb : 4838400 < lastTime - firstTime
      · simp only [ha, hb, if_true, if_false]; omega
      · simp only [ha, hb, if_false]; omega
  have h1 : 302400 ≤ (clampTimespan (lastTime - firstTime)).toNat := by omega
  have h2 : (clampTimespan (lastTime - firstTime)).toNat ≤ 4838400 := by omega
  generalize hcd : (clampTimespan (lastTime - firstTime)).toNat = c at h1 h2
  have hw : t * c < width := by
    calc t * c ≤ powLimit * 4838400 := Nat.mul_le_mul ht h2
      _ < width := by unfold powLimit width; decide
  have hb : (t * c) % width / targetTimespan = t * c / 1209600 := by
    rw [Nat.mod_eq_of_lt hw]; rfl
  have hup : t * c / 1209600 ≤ 4 * t := by
    apply Nat.div_le_of_le_mul
    have := Nat.mul_le_mul_left t h2
    clear hw hb hc hcd ht
    omega
  have hlo : t / 4 ≤ t * c / 1209600 := by
    apply (Nat.le_div_iff_mul_le (by decide)).2
    have h3 := Nat.mul_le_mul_left t h1
    have h4 : t / 4 * 4 * 302400 ≤ t * 302400 := Nat.mul_le_mul_right _ (Nat.div_mul_le_self t 4)
    calc t / 4 * 1209600 = t / 4 * 4 * 302400 := by rw [Nat.mul_assoc]
      _ ≤ t * c := Nat.le_trans h4 h3
  have hr : rawNextTarget t lastTime firstTime =
      (if powLimit < (t * c) % width / targetTimespan then powLimit else (t * c) % width / targetTimespan) := by
    rw [← hcd]; rfl
  rw [hr, hb]
  by_cases hp : powLimit < t * c / 1209600
  · rw [if_pos hp]; exact ⟨by omega, Or.inl rfl⟩
  · rw [if_neg hp]; exact ⟨hup, Or.inr hlo⟩
