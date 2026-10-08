-- Prove2me | solution 1 for ErdosStraus242.family_mod1103
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:39.891807+00:00
-- url     : https://prove2.me/submissions/d04727d5-6fd4-400c-b70f-b603ac45e6d7

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1103 ∈ ({1099, 1095, 1091, 1087, 1079, 1055, 1011, 919, 827, 735, 551} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1103
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1103 * k + n % 1103 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h
  · -- class 1099: alpha = 276, g = 1, beta = 275
    have hnform : n = 1103 * k + 1099 := by omega
    rw [hnform]
    refine ⟨276 * k + 275, 276 * (1103 * k + 1099), 276 * (276 * k + 275) * (1103 * k + 1099), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 276 * k + 275 := by nlinarith
      have hk2 : (0 : ℚ) < 1103 * k + 1099 := by nlinarith
      field_simp
      ring
  · -- class 1095: alpha = 276, g = 2, beta = 274
    have hnform : n = 1103 * k + 1095 := by omega
    rw [hnform]
    refine ⟨276 * k + 274, 276 * (1103 * k + 1095), 138 * (276 * k + 274) * (1103 * k + 1095), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 276 * k + 274 := by nlinarith
      have hk2 : (0 : ℚ) < 1103 * k + 1095 := by nlinarith
      field_simp
      ring
  · -- class 1091: alpha = 276, g = 3, beta = 273
    have hnform : n = 1103 * k + 1091 := by omega
    rw [hnform]
    refine ⟨276 * k + 273, 276 * (1103 * k + 1091), 92 * (276 * k + 273) * (1103 * k + 1091), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 276 * k + 273 := by nlinarith
      have hk2 : (0 : ℚ) < 1103 * k + 1091 := by nlinarith
      field_simp
      ring
  · -- class 1087: alpha = 276, g = 4, beta = 272
    have hnform : n = 1103 * k + 1087 := by omega
    rw [hnform]
    refine ⟨276 * k + 272, 276 * (1103 * k + 1087), 69 * (276 * k + 272) * (1103 * k + 1087), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 276 * k + 272 := by nlinarith
      have hk2 : (0 : ℚ) < 1103 * k + 1087 := by nlinarith
      field_simp
      ring
  · -- class 1079: alpha = 276, g = 6, beta = 270
    have hnform : n = 1103 * k + 1079 := by omega
    rw [hnform]
    refine ⟨276 * k + 270, 276 * (1103 * k + 1079), 46 * (276 * k + 270) * (1103 * k + 1079), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 276 * k + 270 := by nlinarith
      have hk2 : (0 : ℚ) < 1103 * k + 1079 := by nlinarith
      field_simp
      ring
  · -- class 1055: alpha = 276, g = 12, beta = 264
    have hnform : n = 1103 * k + 1055 := by omega
    rw [hnform]
    refine ⟨276 * k + 264, 276 * (1103 * k + 1055), 23 * (276 * k + 264) * (1103 * k + 1055), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 276 * k + 264 := by nlinarith
      have hk2 : (0 : ℚ) < 1103 * k + 1055 := by nlinarith
      field_simp
      ring
  · -- class 1011: alpha = 276, g = 23, beta = 253
    have hnform : n = 1103 * k + 1011 := by omega
    rw [hnform]
    refine ⟨276 * k + 253, 276 * (1103 * k + 1011), 12 * (276 * k + 253) * (1103 * k + 1011), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 276 * k + 253 := by nlinarith
      have hk2 : (0 : ℚ) < 1103 * k + 1011 := by nlinarith
      field_simp
      ring
  · -- class 919: alpha = 276, g = 46, beta = 230
    have hnform : n = 1103 * k + 919 := by omega
    rw [hnform]
    refine ⟨276 * k + 230, 276 * (1103 * k + 919), 6 * (276 * k + 230) * (1103 * k + 919), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 276 * k + 230 := by nlinarith
      have hk2 : (0 : ℚ) < 1103 * k + 919 := by nlinarith
      field_simp
      ring
  · -- class 827: alpha = 276, g = 69, beta = 207
    have hnform : n = 1103 * k + 827 := by omega
    rw [hnform]
    refine ⟨276 * k + 207, 276 * (1103 * k + 827), 4 * (276 * k + 207) * (1103 * k + 827), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 276 * k + 207 := by nlinarith
      have hk2 : (0 : ℚ) < 1103 * k + 827 := by nlinarith
      field_simp
      ring
  · -- class 735: alpha = 276, g = 92, beta = 184
    have hnform : n = 1103 * k + 735 := by omega
    rw [hnform]
    refine ⟨276 * k + 184, 276 * (1103 * k + 735), 3 * (276 * k + 184) * (1103 * k + 735), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 276 * k + 184 := by nlinarith
      have hk2 : (0 : ℚ) < 1103 * k + 735 := by nlinarith
      field_simp
      ring
  · -- class 551: alpha = 276, g = 138, beta = 138
    have hnform : n = 1103 * k + 551 := by omega
    by_cases hk0 : k = 0
    · have h551 : n = 551 := by omega
      rw [h551]
      refine ⟨138, 76039, 5781853482, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨276 * k + 138, 276 * (1103 * k + 551), 2 * (276 * k + 138) * (1103 * k + 551), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 276 * k + 138 := by nlinarith
        have hk2 : (0 : ℚ) < 1103 * k + 551 := by nlinarith
        field_simp
        ring
