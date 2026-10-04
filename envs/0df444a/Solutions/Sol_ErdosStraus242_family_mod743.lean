-- Prove2me | solution 1 for ErdosStraus242.family_mod743
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:27.6444+00:00
-- url     : https://prove2.me/submissions/f9b6ad14-c298-4d22-a6c2-ea94f0f6f4fc

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 743 ∈ ({739, 735, 731, 719, 619, 495, 371} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 743
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 743 * k + n % 743 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 739: alpha = 186, g = 1, beta = 185
    have hnform : n = 743 * k + 739 := by omega
    rw [hnform]
    refine ⟨186 * k + 185, 186 * (743 * k + 739), 186 * (186 * k + 185) * (743 * k + 739), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 186 * k + 185 := by nlinarith
      have hk2 : (0 : ℚ) < 743 * k + 739 := by nlinarith
      field_simp
      ring
  · -- class 735: alpha = 186, g = 2, beta = 184
    have hnform : n = 743 * k + 735 := by omega
    rw [hnform]
    refine ⟨186 * k + 184, 186 * (743 * k + 735), 93 * (186 * k + 184) * (743 * k + 735), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 186 * k + 184 := by nlinarith
      have hk2 : (0 : ℚ) < 743 * k + 735 := by nlinarith
      field_simp
      ring
  · -- class 731: alpha = 186, g = 3, beta = 183
    have hnform : n = 743 * k + 731 := by omega
    rw [hnform]
    refine ⟨186 * k + 183, 186 * (743 * k + 731), 62 * (186 * k + 183) * (743 * k + 731), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 186 * k + 183 := by nlinarith
      have hk2 : (0 : ℚ) < 743 * k + 731 := by nlinarith
      field_simp
      ring
  · -- class 719: alpha = 186, g = 6, beta = 180
    have hnform : n = 743 * k + 719 := by omega
    rw [hnform]
    refine ⟨186 * k + 180, 186 * (743 * k + 719), 31 * (186 * k + 180) * (743 * k + 719), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 186 * k + 180 := by nlinarith
      have hk2 : (0 : ℚ) < 743 * k + 719 := by nlinarith
      field_simp
      ring
  · -- class 619: alpha = 186, g = 31, beta = 155
    have hnform : n = 743 * k + 619 := by omega
    rw [hnform]
    refine ⟨186 * k + 155, 186 * (743 * k + 619), 6 * (186 * k + 155) * (743 * k + 619), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 186 * k + 155 := by nlinarith
      have hk2 : (0 : ℚ) < 743 * k + 619 := by nlinarith
      field_simp
      ring
  · -- class 495: alpha = 186, g = 62, beta = 124
    have hnform : n = 743 * k + 495 := by omega
    rw [hnform]
    refine ⟨186 * k + 124, 186 * (743 * k + 495), 3 * (186 * k + 124) * (743 * k + 495), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 186 * k + 124 := by nlinarith
      have hk2 : (0 : ℚ) < 743 * k + 495 := by nlinarith
      field_simp
      ring
  · -- class 371: alpha = 186, g = 93, beta = 93
    have hnform : n = 743 * k + 371 := by omega
    by_cases hk0 : k = 0
    · have h371 : n = 371 := by omega
      rw [h371]
      refine ⟨93, 34504, 1190491512, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨186 * k + 93, 186 * (743 * k + 371), 2 * (186 * k + 93) * (743 * k + 371), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 186 * k + 93 := by nlinarith
        have hk2 : (0 : ℚ) < 743 * k + 371 := by nlinarith
        field_simp
        ring
