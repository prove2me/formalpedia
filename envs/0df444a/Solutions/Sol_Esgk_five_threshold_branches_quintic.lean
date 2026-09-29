-- Prove2me | solution 1 for Esgk.five_threshold_branches_quintic
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-14T02:17:53.465066+00:00
-- url     : https://prove2.me/submissions/c2f6af9c-bd3e-446a-a1c9-f9ffe3a2bfd7

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

theorem solution
    (n s T C : ℕ) (hs : 0 < s) (hT : 0 < T)
    (hbranches : n ≤ 3 * s ∨ n ≤ s ^ 2 ∨ n ≤ s ∨
      n ^ 2 < 128 * T * s ^ 7 ∨ n ≤ 32 * C * s ^ 5) :
    n ≤ max 3 (max (128 * T) (32 * C)) * s ^ 5 := by
  let A := max 3 (max (128 * T) (32 * C))
  have hAthree : 3 ≤ A := by simp [A]
  have hAfailure : 128 * T ≤ A := by simp [A]
  have hAsuccess : 32 * C ≤ A := by simp [A]
  have hAone : 1 ≤ A := le_trans (by omega) hAthree
  have hsPowOne : s ≤ s ^ 5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hs (by omega : 1 ≤ 5)
  have hsPowTwo : s ^ 2 ≤ s ^ 5 := Nat.pow_le_pow_right hs (by omega)
  rcases hbranches with hCircle | hNonabsolute | hSmall | hFailure | hSuccess
  · calc
      n ≤ 3 * s := hCircle
      _ ≤ A * s := Nat.mul_le_mul_right s hAthree
      _ ≤ A * s ^ 5 := Nat.mul_le_mul_left A hsPowOne
  · calc
      n ≤ s ^ 2 := hNonabsolute
      _ = 1 * s ^ 2 := by simp
      _ ≤ A * s ^ 2 := Nat.mul_le_mul_right (s ^ 2) hAone
      _ ≤ A * s ^ 5 := Nat.mul_le_mul_left A hsPowTwo
  · calc
      n ≤ s := hSmall
      _ ≤ s ^ 5 := hsPowOne
      _ = 1 * s ^ 5 := by simp
      _ ≤ A * s ^ 5 := Nat.mul_le_mul_right (s ^ 5) hAone
  · have hFailurePos : 0 < 128 * T := Nat.mul_pos (by norm_num) hT
    have hFailureCoeffSq : 128 * T ≤ (128 * T) ^ 2 := by
      calc
        128 * T = (128 * T) * 1 := by ring
        _ ≤ (128 * T) * (128 * T) := Nat.mul_le_mul_left _ hFailurePos
        _ = (128 * T) ^ 2 := by ring
    have hsPowSeven : s ^ 7 ≤ s ^ 10 := Nat.pow_le_pow_right hs (by omega)
    have hFailureThreshold :
        128 * T * s ^ 7 ≤ ((128 * T) * s ^ 5) ^ 2 := by
      calc
        128 * T * s ^ 7 ≤ (128 * T) ^ 2 * s ^ 10 := by gcongr
        _ = ((128 * T) * s ^ 5) ^ 2 := by ring
    have hnSq : n ^ 2 < ((128 * T) * s ^ 5) ^ 2 :=
      hFailure.trans_le hFailureThreshold
    have hnFailure : n < (128 * T) * s ^ 5 := by
      by_contra hnot
      have hge : (128 * T) * s ^ 5 ≤ n := Nat.le_of_not_gt hnot
      have hgeSq := Nat.pow_le_pow_left hge 2
      omega
    calc
      n ≤ (128 * T) * s ^ 5 := hnFailure.le
      _ ≤ A * s ^ 5 := Nat.mul_le_mul_right (s ^ 5) hAfailure
  · calc
      n ≤ (32 * C) * s ^ 5 := hSuccess
      _ ≤ A * s ^ 5 := Nat.mul_le_mul_right (s ^ 5) hAsuccess
