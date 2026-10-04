-- Prove2me | solution 1 for ErdosStraus242.family_mod767
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:28.872084+00:00
-- url     : https://prove2.me/submissions/45da5be4-95a5-4742-bfe9-6f5760d449c7

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 767 ∈ ({763, 759, 755, 751, 743, 735, 719, 703, 671, 639, 575, 511, 383} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 767
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 767 * k + n % 767 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h | h | h
  · -- class 763: alpha = 192, g = 1, beta = 191
    have hnform : n = 767 * k + 763 := by omega
    rw [hnform]
    refine ⟨192 * k + 191, 192 * (767 * k + 763), 192 * (192 * k + 191) * (767 * k + 763), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 192 * k + 191 := by nlinarith
      have hk2 : (0 : ℚ) < 767 * k + 763 := by nlinarith
      field_simp
      ring
  · -- class 759: alpha = 192, g = 2, beta = 190
    have hnform : n = 767 * k + 759 := by omega
    rw [hnform]
    refine ⟨192 * k + 190, 192 * (767 * k + 759), 96 * (192 * k + 190) * (767 * k + 759), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 192 * k + 190 := by nlinarith
      have hk2 : (0 : ℚ) < 767 * k + 759 := by nlinarith
      field_simp
      ring
  · -- class 755: alpha = 192, g = 3, beta = 189
    have hnform : n = 767 * k + 755 := by omega
    rw [hnform]
    refine ⟨192 * k + 189, 192 * (767 * k + 755), 64 * (192 * k + 189) * (767 * k + 755), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 192 * k + 189 := by nlinarith
      have hk2 : (0 : ℚ) < 767 * k + 755 := by nlinarith
      field_simp
      ring
  · -- class 751: alpha = 192, g = 4, beta = 188
    have hnform : n = 767 * k + 751 := by omega
    rw [hnform]
    refine ⟨192 * k + 188, 192 * (767 * k + 751), 48 * (192 * k + 188) * (767 * k + 751), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 192 * k + 188 := by nlinarith
      have hk2 : (0 : ℚ) < 767 * k + 751 := by nlinarith
      field_simp
      ring
  · -- class 743: alpha = 192, g = 6, beta = 186
    have hnform : n = 767 * k + 743 := by omega
    rw [hnform]
    refine ⟨192 * k + 186, 192 * (767 * k + 743), 32 * (192 * k + 186) * (767 * k + 743), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 192 * k + 186 := by nlinarith
      have hk2 : (0 : ℚ) < 767 * k + 743 := by nlinarith
      field_simp
      ring
  · -- class 735: alpha = 192, g = 8, beta = 184
    have hnform : n = 767 * k + 735 := by omega
    rw [hnform]
    refine ⟨192 * k + 184, 192 * (767 * k + 735), 24 * (192 * k + 184) * (767 * k + 735), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 192 * k + 184 := by nlinarith
      have hk2 : (0 : ℚ) < 767 * k + 735 := by nlinarith
      field_simp
      ring
  · -- class 719: alpha = 192, g = 12, beta = 180
    have hnform : n = 767 * k + 719 := by omega
    rw [hnform]
    refine ⟨192 * k + 180, 192 * (767 * k + 719), 16 * (192 * k + 180) * (767 * k + 719), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 192 * k + 180 := by nlinarith
      have hk2 : (0 : ℚ) < 767 * k + 719 := by nlinarith
      field_simp
      ring
  · -- class 703: alpha = 192, g = 16, beta = 176
    have hnform : n = 767 * k + 703 := by omega
    rw [hnform]
    refine ⟨192 * k + 176, 192 * (767 * k + 703), 12 * (192 * k + 176) * (767 * k + 703), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 192 * k + 176 := by nlinarith
      have hk2 : (0 : ℚ) < 767 * k + 703 := by nlinarith
      field_simp
      ring
  · -- class 671: alpha = 192, g = 24, beta = 168
    have hnform : n = 767 * k + 671 := by omega
    rw [hnform]
    refine ⟨192 * k + 168, 192 * (767 * k + 671), 8 * (192 * k + 168) * (767 * k + 671), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 192 * k + 168 := by nlinarith
      have hk2 : (0 : ℚ) < 767 * k + 671 := by nlinarith
      field_simp
      ring
  · -- class 639: alpha = 192, g = 32, beta = 160
    have hnform : n = 767 * k + 639 := by omega
    rw [hnform]
    refine ⟨192 * k + 160, 192 * (767 * k + 639), 6 * (192 * k + 160) * (767 * k + 639), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 192 * k + 160 := by nlinarith
      have hk2 : (0 : ℚ) < 767 * k + 639 := by nlinarith
      field_simp
      ring
  · -- class 575: alpha = 192, g = 48, beta = 144
    have hnform : n = 767 * k + 575 := by omega
    rw [hnform]
    refine ⟨192 * k + 144, 192 * (767 * k + 575), 4 * (192 * k + 144) * (767 * k + 575), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 192 * k + 144 := by nlinarith
      have hk2 : (0 : ℚ) < 767 * k + 575 := by nlinarith
      field_simp
      ring
  · -- class 511: alpha = 192, g = 64, beta = 128
    have hnform : n = 767 * k + 511 := by omega
    rw [hnform]
    refine ⟨192 * k + 128, 192 * (767 * k + 511), 3 * (192 * k + 128) * (767 * k + 511), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 192 * k + 128 := by nlinarith
      have hk2 : (0 : ℚ) < 767 * k + 511 := by nlinarith
      field_simp
      ring
  · -- class 383: alpha = 192, g = 96, beta = 96
    have hnform : n = 767 * k + 383 := by omega
    by_cases hk0 : k = 0
    · have h383 : n = 383 := by omega
      rw [h383]
      refine ⟨96, 36769, 1351922592, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨192 * k + 96, 192 * (767 * k + 383), 2 * (192 * k + 96) * (767 * k + 383), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 192 * k + 96 := by nlinarith
        have hk2 : (0 : ℚ) < 767 * k + 383 := by nlinarith
        field_simp
        ring
