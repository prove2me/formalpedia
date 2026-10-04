-- Prove2me | solution 1 for ErdosStraus242.family_mod503
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:35.569303+00:00
-- url     : https://prove2.me/submissions/76404000-3d93-4190-804c-37ca4852759c

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 503 ∈ ({499, 495, 491, 479, 475, 467, 447, 431, 419, 335, 251} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 503
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 503 * k + n % 503 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h
  · -- class 499: alpha = 126, g = 1, beta = 125
    have hnform : n = 503 * k + 499 := by omega
    rw [hnform]
    refine ⟨126 * k + 125, 126 * (503 * k + 499), 126 * (126 * k + 125) * (503 * k + 499), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 126 * k + 125 := by nlinarith
      have hk2 : (0 : ℚ) < 503 * k + 499 := by nlinarith
      field_simp
      ring
  · -- class 495: alpha = 126, g = 2, beta = 124
    have hnform : n = 503 * k + 495 := by omega
    rw [hnform]
    refine ⟨126 * k + 124, 126 * (503 * k + 495), 63 * (126 * k + 124) * (503 * k + 495), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 126 * k + 124 := by nlinarith
      have hk2 : (0 : ℚ) < 503 * k + 495 := by nlinarith
      field_simp
      ring
  · -- class 491: alpha = 126, g = 3, beta = 123
    have hnform : n = 503 * k + 491 := by omega
    rw [hnform]
    refine ⟨126 * k + 123, 126 * (503 * k + 491), 42 * (126 * k + 123) * (503 * k + 491), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 126 * k + 123 := by nlinarith
      have hk2 : (0 : ℚ) < 503 * k + 491 := by nlinarith
      field_simp
      ring
  · -- class 479: alpha = 126, g = 6, beta = 120
    have hnform : n = 503 * k + 479 := by omega
    rw [hnform]
    refine ⟨126 * k + 120, 126 * (503 * k + 479), 21 * (126 * k + 120) * (503 * k + 479), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 126 * k + 120 := by nlinarith
      have hk2 : (0 : ℚ) < 503 * k + 479 := by nlinarith
      field_simp
      ring
  · -- class 475: alpha = 126, g = 7, beta = 119
    have hnform : n = 503 * k + 475 := by omega
    rw [hnform]
    refine ⟨126 * k + 119, 126 * (503 * k + 475), 18 * (126 * k + 119) * (503 * k + 475), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 126 * k + 119 := by nlinarith
      have hk2 : (0 : ℚ) < 503 * k + 475 := by nlinarith
      field_simp
      ring
  · -- class 467: alpha = 126, g = 9, beta = 117
    have hnform : n = 503 * k + 467 := by omega
    rw [hnform]
    refine ⟨126 * k + 117, 126 * (503 * k + 467), 14 * (126 * k + 117) * (503 * k + 467), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 126 * k + 117 := by nlinarith
      have hk2 : (0 : ℚ) < 503 * k + 467 := by nlinarith
      field_simp
      ring
  · -- class 447: alpha = 126, g = 14, beta = 112
    have hnform : n = 503 * k + 447 := by omega
    rw [hnform]
    refine ⟨126 * k + 112, 126 * (503 * k + 447), 9 * (126 * k + 112) * (503 * k + 447), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 126 * k + 112 := by nlinarith
      have hk2 : (0 : ℚ) < 503 * k + 447 := by nlinarith
      field_simp
      ring
  · -- class 431: alpha = 126, g = 18, beta = 108
    have hnform : n = 503 * k + 431 := by omega
    rw [hnform]
    refine ⟨126 * k + 108, 126 * (503 * k + 431), 7 * (126 * k + 108) * (503 * k + 431), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 126 * k + 108 := by nlinarith
      have hk2 : (0 : ℚ) < 503 * k + 431 := by nlinarith
      field_simp
      ring
  · -- class 419: alpha = 126, g = 21, beta = 105
    have hnform : n = 503 * k + 419 := by omega
    rw [hnform]
    refine ⟨126 * k + 105, 126 * (503 * k + 419), 6 * (126 * k + 105) * (503 * k + 419), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 126 * k + 105 := by nlinarith
      have hk2 : (0 : ℚ) < 503 * k + 419 := by nlinarith
      field_simp
      ring
  · -- class 335: alpha = 126, g = 42, beta = 84
    have hnform : n = 503 * k + 335 := by omega
    rw [hnform]
    refine ⟨126 * k + 84, 126 * (503 * k + 335), 3 * (126 * k + 84) * (503 * k + 335), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 126 * k + 84 := by nlinarith
      have hk2 : (0 : ℚ) < 503 * k + 335 := by nlinarith
      field_simp
      ring
  · -- class 251: alpha = 126, g = 63, beta = 63
    have hnform : n = 503 * k + 251 := by omega
    by_cases hk0 : k = 0
    · have h251 : n = 251 := by omega
      rw [h251]
      refine ⟨63, 15814, 250066782, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨126 * k + 63, 126 * (503 * k + 251), 2 * (126 * k + 63) * (503 * k + 251), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 126 * k + 63 := by nlinarith
        have hk2 : (0 : ℚ) < 503 * k + 251 := by nlinarith
        field_simp
        ring
