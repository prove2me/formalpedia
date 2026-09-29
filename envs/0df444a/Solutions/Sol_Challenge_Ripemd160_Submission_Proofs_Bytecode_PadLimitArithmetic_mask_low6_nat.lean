-- Prove2me | solution 1 for Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLimitArithmetic.mask_low6_nat
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T19:41:24.949976+00:00
-- url     : https://prove2.me/submissions/28a57cb3-894a-45e2-bae5-b9dc6cf17f03

import Mathlib
theorem solution (n : Nat) (hn : n < 2 ^ 256) :
    (2 ^ 256 - 1 - 63) &&& n = n >>> 6 <<< 6 := by
  have hm : (2:Nat) ^ 256 - 1 - 63 = (2 ^ 250 - 1) <<< 6 := by
    rw [Nat.shiftLeft_eq]
    have h : (2:Nat) ^ 250 * 2 ^ 6 = 2 ^ 256 := by rw [← pow_add]
    have h2 : (1:Nat) ≤ 2 ^ 250 := Nat.one_le_two_pow
    omega
  rw [hm]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases h6 : i ≥ 6
  · by_cases h256 : i < 256
    · rw [show 6 + (i - 6) = i by omega]
      simp [h6, show i - 6 < 250 by omega]
    · have hle : (2:Nat) ^ 256 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hz : n.testBit i = false := Nat.testBit_lt_two_pow (by omega)
      rw [show 6 + (i - 6) = i by omega]
      simp [h6, hz]
  · simp [h6]
