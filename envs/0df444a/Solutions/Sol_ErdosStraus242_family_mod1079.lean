-- Prove2me | solution 1 for ErdosStraus242.family_mod1079
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:38.443978+00:00
-- url     : https://prove2.me/submissions/50923214-c85e-4235-9c94-39f096750207

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1079 ∈ ({1075, 1071, 1067, 1059, 1055, 1043, 1039, 1019, 1007, 971, 959, 899, 863, 719, 539} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1079
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1079 * k + n % 1079 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · -- class 1075: alpha = 270, g = 1, beta = 269
    have hnform : n = 1079 * k + 1075 := by omega
    rw [hnform]
    refine ⟨270 * k + 269, 270 * (1079 * k + 1075), 270 * (270 * k + 269) * (1079 * k + 1075), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 270 * k + 269 := by nlinarith
      have hk2 : (0 : ℚ) < 1079 * k + 1075 := by nlinarith
      field_simp
      ring
  · -- class 1071: alpha = 270, g = 2, beta = 268
    have hnform : n = 1079 * k + 1071 := by omega
    rw [hnform]
    refine ⟨270 * k + 268, 270 * (1079 * k + 1071), 135 * (270 * k + 268) * (1079 * k + 1071), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 270 * k + 268 := by nlinarith
      have hk2 : (0 : ℚ) < 1079 * k + 1071 := by nlinarith
      field_simp
      ring
  · -- class 1067: alpha = 270, g = 3, beta = 267
    have hnform : n = 1079 * k + 1067 := by omega
    rw [hnform]
    refine ⟨270 * k + 267, 270 * (1079 * k + 1067), 90 * (270 * k + 267) * (1079 * k + 1067), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 270 * k + 267 := by nlinarith
      have hk2 : (0 : ℚ) < 1079 * k + 1067 := by nlinarith
      field_simp
      ring
  · -- class 1059: alpha = 270, g = 5, beta = 265
    have hnform : n = 1079 * k + 1059 := by omega
    rw [hnform]
    refine ⟨270 * k + 265, 270 * (1079 * k + 1059), 54 * (270 * k + 265) * (1079 * k + 1059), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 270 * k + 265 := by nlinarith
      have hk2 : (0 : ℚ) < 1079 * k + 1059 := by nlinarith
      field_simp
      ring
  · -- class 1055: alpha = 270, g = 6, beta = 264
    have hnform : n = 1079 * k + 1055 := by omega
    rw [hnform]
    refine ⟨270 * k + 264, 270 * (1079 * k + 1055), 45 * (270 * k + 264) * (1079 * k + 1055), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 270 * k + 264 := by nlinarith
      have hk2 : (0 : ℚ) < 1079 * k + 1055 := by nlinarith
      field_simp
      ring
  · -- class 1043: alpha = 270, g = 9, beta = 261
    have hnform : n = 1079 * k + 1043 := by omega
    rw [hnform]
    refine ⟨270 * k + 261, 270 * (1079 * k + 1043), 30 * (270 * k + 261) * (1079 * k + 1043), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 270 * k + 261 := by nlinarith
      have hk2 : (0 : ℚ) < 1079 * k + 1043 := by nlinarith
      field_simp
      ring
  · -- class 1039: alpha = 270, g = 10, beta = 260
    have hnform : n = 1079 * k + 1039 := by omega
    rw [hnform]
    refine ⟨270 * k + 260, 270 * (1079 * k + 1039), 27 * (270 * k + 260) * (1079 * k + 1039), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 270 * k + 260 := by nlinarith
      have hk2 : (0 : ℚ) < 1079 * k + 1039 := by nlinarith
      field_simp
      ring
  · -- class 1019: alpha = 270, g = 15, beta = 255
    have hnform : n = 1079 * k + 1019 := by omega
    rw [hnform]
    refine ⟨270 * k + 255, 270 * (1079 * k + 1019), 18 * (270 * k + 255) * (1079 * k + 1019), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 270 * k + 255 := by nlinarith
      have hk2 : (0 : ℚ) < 1079 * k + 1019 := by nlinarith
      field_simp
      ring
  · -- class 1007: alpha = 270, g = 18, beta = 252
    have hnform : n = 1079 * k + 1007 := by omega
    rw [hnform]
    refine ⟨270 * k + 252, 270 * (1079 * k + 1007), 15 * (270 * k + 252) * (1079 * k + 1007), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 270 * k + 252 := by nlinarith
      have hk2 : (0 : ℚ) < 1079 * k + 1007 := by nlinarith
      field_simp
      ring
  · -- class 971: alpha = 270, g = 27, beta = 243
    have hnform : n = 1079 * k + 971 := by omega
    rw [hnform]
    refine ⟨270 * k + 243, 270 * (1079 * k + 971), 10 * (270 * k + 243) * (1079 * k + 971), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 270 * k + 243 := by nlinarith
      have hk2 : (0 : ℚ) < 1079 * k + 971 := by nlinarith
      field_simp
      ring
  · -- class 959: alpha = 270, g = 30, beta = 240
    have hnform : n = 1079 * k + 959 := by omega
    rw [hnform]
    refine ⟨270 * k + 240, 270 * (1079 * k + 959), 9 * (270 * k + 240) * (1079 * k + 959), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 270 * k + 240 := by nlinarith
      have hk2 : (0 : ℚ) < 1079 * k + 959 := by nlinarith
      field_simp
      ring
  · -- class 899: alpha = 270, g = 45, beta = 225
    have hnform : n = 1079 * k + 899 := by omega
    rw [hnform]
    refine ⟨270 * k + 225, 270 * (1079 * k + 899), 6 * (270 * k + 225) * (1079 * k + 899), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 270 * k + 225 := by nlinarith
      have hk2 : (0 : ℚ) < 1079 * k + 899 := by nlinarith
      field_simp
      ring
  · -- class 863: alpha = 270, g = 54, beta = 216
    have hnform : n = 1079 * k + 863 := by omega
    rw [hnform]
    refine ⟨270 * k + 216, 270 * (1079 * k + 863), 5 * (270 * k + 216) * (1079 * k + 863), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 270 * k + 216 := by nlinarith
      have hk2 : (0 : ℚ) < 1079 * k + 863 := by nlinarith
      field_simp
      ring
  · -- class 719: alpha = 270, g = 90, beta = 180
    have hnform : n = 1079 * k + 719 := by omega
    rw [hnform]
    refine ⟨270 * k + 180, 270 * (1079 * k + 719), 3 * (270 * k + 180) * (1079 * k + 719), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 270 * k + 180 := by nlinarith
      have hk2 : (0 : ℚ) < 1079 * k + 719 := by nlinarith
      field_simp
      ring
  · -- class 539: alpha = 270, g = 135, beta = 135
    have hnform : n = 1079 * k + 539 := by omega
    by_cases hk0 : k = 0
    · have h539 : n = 539 := by omega
      rw [h539]
      refine ⟨135, 72766, 5294817990, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨270 * k + 135, 270 * (1079 * k + 539), 2 * (270 * k + 135) * (1079 * k + 539), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 270 * k + 135 := by nlinarith
        have hk2 : (0 : ℚ) < 1079 * k + 539 := by nlinarith
        field_simp
        ring
