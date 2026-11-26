-- Prove2me | solution 1 for FirstPassageLinearTransport.multiplicativeHitCount_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:57.253377+00:00
-- url     : https://prove2.me/submissions/ab9240e5-ce5c-45a4-8a3a-bc2eeee6f190

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_multiplicativeHitCount_of_crossed
import Theorems.Thm_FirstPassageLinearTransport_multiplicativeHitCount_succ_of_safe
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (u : ℝ) (r : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (multiplicativeHitCount u r z : ℝ) * u ≤ (2 : ℝ) ^ r * z := by
  induction r generalizing z with
  | zero =>
      by_cases hcross : u < z
      · rw [multiplicativeHitCount_of_crossed hcross]
        simpa using hcross.le
      · simp [multiplicativeHitCount, crossesMultiplicativeFrom, hcross, hz]
  | succ r ihr =>
      by_cases hcross : u < z
      · rw [multiplicativeHitCount_of_crossed hcross]
        norm_num only [Nat.cast_pow, Nat.cast_ofNat]
        exact mul_le_mul_of_nonneg_left hcross.le (by positivity)
      · rw [multiplicativeHitCount_succ_of_safe hcross]
        push_cast
        have hright := ihr (z * (3 / 2)) (by positivity)
        have hleft := ihr (z * (1 / 2)) (by positivity)
        calc
          ((multiplicativeHitCount u r (z * (3 / 2)) : ℝ) +
              (multiplicativeHitCount u r (z * (1 / 2)) : ℝ)) * u =
              (multiplicativeHitCount u r (z * (3 / 2)) : ℝ) * u +
                (multiplicativeHitCount u r (z * (1 / 2)) : ℝ) * u := by ring
          _ ≤ (2 : ℝ) ^ r * (z * (3 / 2)) +
                (2 : ℝ) ^ r * (z * (1 / 2)) := add_le_add hright hleft
          _ = (2 : ℝ) ^ (r + 1) * z := by rw [pow_succ]; ring
end FirstPassageLinearTransport
