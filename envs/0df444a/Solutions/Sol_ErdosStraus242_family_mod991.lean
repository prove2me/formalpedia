-- Prove2me | solution 1 for ErdosStraus242.family_mod991
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:13:08.400726+00:00
-- url     : https://prove2.me/submissions/3068cd8e-1172-45a3-bddf-c1a15ab3acd8

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 991 ∈ ({987, 983, 975, 959, 867, 743, 495} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 991
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 991 * k + n % 991 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 987: alpha = 248, g = 1, beta = 247
    have hnform : n = 991 * k + 987 := by omega
    rw [hnform]
    refine ⟨248 * k + 247, 248 * (991 * k + 987), 248 * (248 * k + 247) * (991 * k + 987), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 248 * k + 247 := by nlinarith
      have hk2 : (0 : ℚ) < 991 * k + 987 := by nlinarith
      field_simp
      ring
  · -- class 983: alpha = 248, g = 2, beta = 246
    have hnform : n = 991 * k + 983 := by omega
    rw [hnform]
    refine ⟨248 * k + 246, 248 * (991 * k + 983), 124 * (248 * k + 246) * (991 * k + 983), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 248 * k + 246 := by nlinarith
      have hk2 : (0 : ℚ) < 991 * k + 983 := by nlinarith
      field_simp
      ring
  · -- class 975: alpha = 248, g = 4, beta = 244
    have hnform : n = 991 * k + 975 := by omega
    rw [hnform]
    refine ⟨248 * k + 244, 248 * (991 * k + 975), 62 * (248 * k + 244) * (991 * k + 975), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 248 * k + 244 := by nlinarith
      have hk2 : (0 : ℚ) < 991 * k + 975 := by nlinarith
      field_simp
      ring
  · -- class 959: alpha = 248, g = 8, beta = 240
    have hnform : n = 991 * k + 959 := by omega
    rw [hnform]
    refine ⟨248 * k + 240, 248 * (991 * k + 959), 31 * (248 * k + 240) * (991 * k + 959), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 248 * k + 240 := by nlinarith
      have hk2 : (0 : ℚ) < 991 * k + 959 := by nlinarith
      field_simp
      ring
  · -- class 867: alpha = 248, g = 31, beta = 217
    have hnform : n = 991 * k + 867 := by omega
    rw [hnform]
    refine ⟨248 * k + 217, 248 * (991 * k + 867), 8 * (248 * k + 217) * (991 * k + 867), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 248 * k + 217 := by nlinarith
      have hk2 : (0 : ℚ) < 991 * k + 867 := by nlinarith
      field_simp
      ring
  · -- class 743: alpha = 248, g = 62, beta = 186
    have hnform : n = 991 * k + 743 := by omega
    rw [hnform]
    refine ⟨248 * k + 186, 248 * (991 * k + 743), 4 * (248 * k + 186) * (991 * k + 743), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 248 * k + 186 := by nlinarith
      have hk2 : (0 : ℚ) < 991 * k + 743 := by nlinarith
      field_simp
      ring
  · -- class 495: alpha = 248, g = 124, beta = 124
    have hnform : n = 991 * k + 495 := by omega
    by_cases hk0 : k = 0
    · have h495 : n = 495 := by omega
      rw [h495]
      refine ⟨124, 61381, 3767565780, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨248 * k + 124, 248 * (991 * k + 495), 2 * (248 * k + 124) * (991 * k + 495), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 248 * k + 124 := by nlinarith
        have hk2 : (0 : ℚ) < 991 * k + 495 := by nlinarith
        field_simp
        ring
