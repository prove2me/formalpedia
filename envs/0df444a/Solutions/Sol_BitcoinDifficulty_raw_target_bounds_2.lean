-- Prove2me | solution 2 for BitcoinDifficulty.raw_target_bounds
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:15:09.815622+00:00
-- url     : https://prove2.me/submissions/3299be91-4f73-482d-89a5-87fd1fddbd62

import Definitions.Def_BitcoinDifficulty
import Theorems.Thm_BitcoinPow_clamp_bounds
import Theorems.Thm_BitcoinPow_getCompact_le
import Theorems.Thm_BitcoinPow_nextWork_le_powLimit
import Theorems.Thm_BitcoinPow_round_mono
import Theorems.Thm_BitcoinDifficulty_no_wrap

open BitcoinDifficulty BitcoinPow

private theorem clamp_nat_bounds (actual : Int) :
    302400 ≤ (clampTimespan actual).toNat ∧ (clampTimespan actual).toNat ≤ 4838400 := by
  have h := BitcoinPow.clamp_bounds actual
  simp only [targetTimespan] at h
  omega

/-- **The raw target moves by at most a factor of four.** For a last target `t ≤ powLimit` and any
timestamps: `t / 4 ≤ rawNextTarget t lastTime firstTime` unless the cap binds, and
`rawNextTarget t lastTime firstTime ≤ 4 * t`. -/
theorem solution (t : Nat) (ht : t ≤ BitcoinPow.powLimit) (lastTime firstTime : Int) :
    BitcoinDifficulty.rawNextTarget t lastTime firstTime ≤ 4 * t ∧
    (BitcoinDifficulty.rawNextTarget t lastTime firstTime = BitcoinPow.powLimit ∨
      t / 4 ≤ BitcoinDifficulty.rawNextTarget t lastTime firstTime) := by
  have hT : targetTimespan = 1209600 := rfl
  simp only [rawNextTarget, hT]
  obtain ⟨hlo, hhi⟩ := clamp_nat_bounds (lastTime - firstTime)
  have hnw := BitcoinDifficulty.no_wrap t ht _ hhi
  rw [Nat.mod_eq_of_lt hnw]
  -- upper: t * ts / 1209600 ≤ t * 4838400 / 1209600 = 4 t
  have hup : t * (clampTimespan (lastTime - firstTime)).toNat / 1209600 ≤ 4 * t := by
    apply Nat.div_le_of_le_mul
    have := Nat.mul_le_mul_left t hhi
    omega
  -- lower: t * ts / 1209600 ≥ t * 302400 / 1209600 = t / 4
  have hlow : t / 4 ≤ t * (clampTimespan (lastTime - firstTime)).toNat / 1209600 := by
    have h4 : t / 4 = t * 302400 / 1209600 := by
      rw [show (1209600 : Nat) = 302400 * 4 by rfl, show t * 302400 = 302400 * t by omega]
      rw [Nat.mul_div_mul_left _ _ (by decide)]
    rw [h4]
    exact Nat.div_le_div_right (Nat.mul_le_mul_left t hlo)
  constructor
  · split
    · omega
    · exact hup
  · split
    · exact Or.inl rfl
    · exact Or.inr hlow
