-- Prove2me | solution 1 for ErdosStraus242.family_mod1151
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:42.698165+00:00
-- url     : https://prove2.me/submissions/77863e50-dcfc-4b51-898c-904c07fae332

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1151 ∈ ({1147, 1143, 1139, 1135, 1127, 1119, 1115, 1103, 1087, 1079, 1055, 1023, 1007, 959, 863, 767, 575} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1151
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1151 * k + n % 1151 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · -- class 1147: alpha = 288, g = 1, beta = 287
    have hnform : n = 1151 * k + 1147 := by omega
    rw [hnform]
    refine ⟨288 * k + 287, 288 * (1151 * k + 1147), 288 * (288 * k + 287) * (1151 * k + 1147), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 287 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 1147 := by nlinarith
      field_simp
      ring
  · -- class 1143: alpha = 288, g = 2, beta = 286
    have hnform : n = 1151 * k + 1143 := by omega
    rw [hnform]
    refine ⟨288 * k + 286, 288 * (1151 * k + 1143), 144 * (288 * k + 286) * (1151 * k + 1143), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 286 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 1143 := by nlinarith
      field_simp
      ring
  · -- class 1139: alpha = 288, g = 3, beta = 285
    have hnform : n = 1151 * k + 1139 := by omega
    rw [hnform]
    refine ⟨288 * k + 285, 288 * (1151 * k + 1139), 96 * (288 * k + 285) * (1151 * k + 1139), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 285 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 1139 := by nlinarith
      field_simp
      ring
  · -- class 1135: alpha = 288, g = 4, beta = 284
    have hnform : n = 1151 * k + 1135 := by omega
    rw [hnform]
    refine ⟨288 * k + 284, 288 * (1151 * k + 1135), 72 * (288 * k + 284) * (1151 * k + 1135), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 284 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 1135 := by nlinarith
      field_simp
      ring
  · -- class 1127: alpha = 288, g = 6, beta = 282
    have hnform : n = 1151 * k + 1127 := by omega
    rw [hnform]
    refine ⟨288 * k + 282, 288 * (1151 * k + 1127), 48 * (288 * k + 282) * (1151 * k + 1127), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 282 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 1127 := by nlinarith
      field_simp
      ring
  · -- class 1119: alpha = 288, g = 8, beta = 280
    have hnform : n = 1151 * k + 1119 := by omega
    rw [hnform]
    refine ⟨288 * k + 280, 288 * (1151 * k + 1119), 36 * (288 * k + 280) * (1151 * k + 1119), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 280 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 1119 := by nlinarith
      field_simp
      ring
  · -- class 1115: alpha = 288, g = 9, beta = 279
    have hnform : n = 1151 * k + 1115 := by omega
    rw [hnform]
    refine ⟨288 * k + 279, 288 * (1151 * k + 1115), 32 * (288 * k + 279) * (1151 * k + 1115), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 279 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 1115 := by nlinarith
      field_simp
      ring
  · -- class 1103: alpha = 288, g = 12, beta = 276
    have hnform : n = 1151 * k + 1103 := by omega
    rw [hnform]
    refine ⟨288 * k + 276, 288 * (1151 * k + 1103), 24 * (288 * k + 276) * (1151 * k + 1103), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 276 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 1103 := by nlinarith
      field_simp
      ring
  · -- class 1087: alpha = 288, g = 16, beta = 272
    have hnform : n = 1151 * k + 1087 := by omega
    rw [hnform]
    refine ⟨288 * k + 272, 288 * (1151 * k + 1087), 18 * (288 * k + 272) * (1151 * k + 1087), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 272 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 1087 := by nlinarith
      field_simp
      ring
  · -- class 1079: alpha = 288, g = 18, beta = 270
    have hnform : n = 1151 * k + 1079 := by omega
    rw [hnform]
    refine ⟨288 * k + 270, 288 * (1151 * k + 1079), 16 * (288 * k + 270) * (1151 * k + 1079), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 270 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 1079 := by nlinarith
      field_simp
      ring
  · -- class 1055: alpha = 288, g = 24, beta = 264
    have hnform : n = 1151 * k + 1055 := by omega
    rw [hnform]
    refine ⟨288 * k + 264, 288 * (1151 * k + 1055), 12 * (288 * k + 264) * (1151 * k + 1055), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 264 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 1055 := by nlinarith
      field_simp
      ring
  · -- class 1023: alpha = 288, g = 32, beta = 256
    have hnform : n = 1151 * k + 1023 := by omega
    rw [hnform]
    refine ⟨288 * k + 256, 288 * (1151 * k + 1023), 9 * (288 * k + 256) * (1151 * k + 1023), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 256 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 1023 := by nlinarith
      field_simp
      ring
  · -- class 1007: alpha = 288, g = 36, beta = 252
    have hnform : n = 1151 * k + 1007 := by omega
    rw [hnform]
    refine ⟨288 * k + 252, 288 * (1151 * k + 1007), 8 * (288 * k + 252) * (1151 * k + 1007), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 252 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 1007 := by nlinarith
      field_simp
      ring
  · -- class 959: alpha = 288, g = 48, beta = 240
    have hnform : n = 1151 * k + 959 := by omega
    rw [hnform]
    refine ⟨288 * k + 240, 288 * (1151 * k + 959), 6 * (288 * k + 240) * (1151 * k + 959), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 240 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 959 := by nlinarith
      field_simp
      ring
  · -- class 863: alpha = 288, g = 72, beta = 216
    have hnform : n = 1151 * k + 863 := by omega
    rw [hnform]
    refine ⟨288 * k + 216, 288 * (1151 * k + 863), 4 * (288 * k + 216) * (1151 * k + 863), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 216 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 863 := by nlinarith
      field_simp
      ring
  · -- class 767: alpha = 288, g = 96, beta = 192
    have hnform : n = 1151 * k + 767 := by omega
    rw [hnform]
    refine ⟨288 * k + 192, 288 * (1151 * k + 767), 3 * (288 * k + 192) * (1151 * k + 767), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 288 * k + 192 := by nlinarith
      have hk2 : (0 : ℚ) < 1151 * k + 767 := by nlinarith
      field_simp
      ring
  · -- class 575: alpha = 288, g = 144, beta = 144
    have hnform : n = 1151 * k + 575 := by omega
    by_cases hk0 : k = 0
    · have h575 : n = 575 := by omega
      rw [h575]
      refine ⟨144, 82801, 6855922800, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨288 * k + 144, 288 * (1151 * k + 575), 2 * (288 * k + 144) * (1151 * k + 575), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 288 * k + 144 := by nlinarith
        have hk2 : (0 : ℚ) < 1151 * k + 575 := by nlinarith
        field_simp
        ring
