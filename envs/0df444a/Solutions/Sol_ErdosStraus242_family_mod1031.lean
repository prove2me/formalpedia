-- Prove2me | solution 1 for ErdosStraus242.family_mod1031
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:35.970279+00:00
-- url     : https://prove2.me/submissions/a44525ef-d6b4-45b1-b24c-c95233d20355

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1031 ∈ ({1027, 1023, 1019, 1007, 859, 687, 515} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1031
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1031 * k + n % 1031 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 1027: alpha = 258, g = 1, beta = 257
    have hnform : n = 1031 * k + 1027 := by omega
    rw [hnform]
    refine ⟨258 * k + 257, 258 * (1031 * k + 1027), 258 * (258 * k + 257) * (1031 * k + 1027), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 258 * k + 257 := by nlinarith
      have hk2 : (0 : ℚ) < 1031 * k + 1027 := by nlinarith
      field_simp
      ring
  · -- class 1023: alpha = 258, g = 2, beta = 256
    have hnform : n = 1031 * k + 1023 := by omega
    rw [hnform]
    refine ⟨258 * k + 256, 258 * (1031 * k + 1023), 129 * (258 * k + 256) * (1031 * k + 1023), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 258 * k + 256 := by nlinarith
      have hk2 : (0 : ℚ) < 1031 * k + 1023 := by nlinarith
      field_simp
      ring
  · -- class 1019: alpha = 258, g = 3, beta = 255
    have hnform : n = 1031 * k + 1019 := by omega
    rw [hnform]
    refine ⟨258 * k + 255, 258 * (1031 * k + 1019), 86 * (258 * k + 255) * (1031 * k + 1019), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 258 * k + 255 := by nlinarith
      have hk2 : (0 : ℚ) < 1031 * k + 1019 := by nlinarith
      field_simp
      ring
  · -- class 1007: alpha = 258, g = 6, beta = 252
    have hnform : n = 1031 * k + 1007 := by omega
    rw [hnform]
    refine ⟨258 * k + 252, 258 * (1031 * k + 1007), 43 * (258 * k + 252) * (1031 * k + 1007), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 258 * k + 252 := by nlinarith
      have hk2 : (0 : ℚ) < 1031 * k + 1007 := by nlinarith
      field_simp
      ring
  · -- class 859: alpha = 258, g = 43, beta = 215
    have hnform : n = 1031 * k + 859 := by omega
    rw [hnform]
    refine ⟨258 * k + 215, 258 * (1031 * k + 859), 6 * (258 * k + 215) * (1031 * k + 859), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 258 * k + 215 := by nlinarith
      have hk2 : (0 : ℚ) < 1031 * k + 859 := by nlinarith
      field_simp
      ring
  · -- class 687: alpha = 258, g = 86, beta = 172
    have hnform : n = 1031 * k + 687 := by omega
    rw [hnform]
    refine ⟨258 * k + 172, 258 * (1031 * k + 687), 3 * (258 * k + 172) * (1031 * k + 687), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 258 * k + 172 := by nlinarith
      have hk2 : (0 : ℚ) < 1031 * k + 687 := by nlinarith
      field_simp
      ring
  · -- class 515: alpha = 258, g = 129, beta = 129
    have hnform : n = 1031 * k + 515 := by omega
    by_cases hk0 : k = 0
    · have h515 : n = 515 := by omega
      rw [h515]
      refine ⟨129, 66436, 4413675660, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨258 * k + 129, 258 * (1031 * k + 515), 2 * (258 * k + 129) * (1031 * k + 515), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 258 * k + 129 := by nlinarith
        have hk2 : (0 : ℚ) < 1031 * k + 515 := by nlinarith
        field_simp
        ring
