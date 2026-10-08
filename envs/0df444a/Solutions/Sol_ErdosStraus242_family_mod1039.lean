-- Prove2me | solution 1 for ErdosStraus242.family_mod1039
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:36.461103+00:00
-- url     : https://prove2.me/submissions/016446e1-28b7-4e05-ba09-b033323a3c3c

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1039 ∈ ({1035, 1031, 1023, 1019, 999, 987, 959, 935, 831, 779, 519} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1039
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1039 * k + n % 1039 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h
  · -- class 1035: alpha = 260, g = 1, beta = 259
    have hnform : n = 1039 * k + 1035 := by omega
    rw [hnform]
    refine ⟨260 * k + 259, 260 * (1039 * k + 1035), 260 * (260 * k + 259) * (1039 * k + 1035), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 260 * k + 259 := by nlinarith
      have hk2 : (0 : ℚ) < 1039 * k + 1035 := by nlinarith
      field_simp
      ring
  · -- class 1031: alpha = 260, g = 2, beta = 258
    have hnform : n = 1039 * k + 1031 := by omega
    rw [hnform]
    refine ⟨260 * k + 258, 260 * (1039 * k + 1031), 130 * (260 * k + 258) * (1039 * k + 1031), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 260 * k + 258 := by nlinarith
      have hk2 : (0 : ℚ) < 1039 * k + 1031 := by nlinarith
      field_simp
      ring
  · -- class 1023: alpha = 260, g = 4, beta = 256
    have hnform : n = 1039 * k + 1023 := by omega
    rw [hnform]
    refine ⟨260 * k + 256, 260 * (1039 * k + 1023), 65 * (260 * k + 256) * (1039 * k + 1023), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 260 * k + 256 := by nlinarith
      have hk2 : (0 : ℚ) < 1039 * k + 1023 := by nlinarith
      field_simp
      ring
  · -- class 1019: alpha = 260, g = 5, beta = 255
    have hnform : n = 1039 * k + 1019 := by omega
    rw [hnform]
    refine ⟨260 * k + 255, 260 * (1039 * k + 1019), 52 * (260 * k + 255) * (1039 * k + 1019), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 260 * k + 255 := by nlinarith
      have hk2 : (0 : ℚ) < 1039 * k + 1019 := by nlinarith
      field_simp
      ring
  · -- class 999: alpha = 260, g = 10, beta = 250
    have hnform : n = 1039 * k + 999 := by omega
    rw [hnform]
    refine ⟨260 * k + 250, 260 * (1039 * k + 999), 26 * (260 * k + 250) * (1039 * k + 999), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 260 * k + 250 := by nlinarith
      have hk2 : (0 : ℚ) < 1039 * k + 999 := by nlinarith
      field_simp
      ring
  · -- class 987: alpha = 260, g = 13, beta = 247
    have hnform : n = 1039 * k + 987 := by omega
    rw [hnform]
    refine ⟨260 * k + 247, 260 * (1039 * k + 987), 20 * (260 * k + 247) * (1039 * k + 987), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 260 * k + 247 := by nlinarith
      have hk2 : (0 : ℚ) < 1039 * k + 987 := by nlinarith
      field_simp
      ring
  · -- class 959: alpha = 260, g = 20, beta = 240
    have hnform : n = 1039 * k + 959 := by omega
    rw [hnform]
    refine ⟨260 * k + 240, 260 * (1039 * k + 959), 13 * (260 * k + 240) * (1039 * k + 959), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 260 * k + 240 := by nlinarith
      have hk2 : (0 : ℚ) < 1039 * k + 959 := by nlinarith
      field_simp
      ring
  · -- class 935: alpha = 260, g = 26, beta = 234
    have hnform : n = 1039 * k + 935 := by omega
    rw [hnform]
    refine ⟨260 * k + 234, 260 * (1039 * k + 935), 10 * (260 * k + 234) * (1039 * k + 935), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 260 * k + 234 := by nlinarith
      have hk2 : (0 : ℚ) < 1039 * k + 935 := by nlinarith
      field_simp
      ring
  · -- class 831: alpha = 260, g = 52, beta = 208
    have hnform : n = 1039 * k + 831 := by omega
    rw [hnform]
    refine ⟨260 * k + 208, 260 * (1039 * k + 831), 5 * (260 * k + 208) * (1039 * k + 831), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 260 * k + 208 := by nlinarith
      have hk2 : (0 : ℚ) < 1039 * k + 831 := by nlinarith
      field_simp
      ring
  · -- class 779: alpha = 260, g = 65, beta = 195
    have hnform : n = 1039 * k + 779 := by omega
    rw [hnform]
    refine ⟨260 * k + 195, 260 * (1039 * k + 779), 4 * (260 * k + 195) * (1039 * k + 779), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 260 * k + 195 := by nlinarith
      have hk2 : (0 : ℚ) < 1039 * k + 779 := by nlinarith
      field_simp
      ring
  · -- class 519: alpha = 260, g = 130, beta = 130
    have hnform : n = 1039 * k + 519 := by omega
    by_cases hk0 : k = 0
    · have h519 : n = 519 := by omega
      rw [h519]
      refine ⟨130, 67471, 4552268370, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨260 * k + 130, 260 * (1039 * k + 519), 2 * (260 * k + 130) * (1039 * k + 519), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 260 * k + 130 := by nlinarith
        have hk2 : (0 : ℚ) < 1039 * k + 519 := by nlinarith
        field_simp
        ring
