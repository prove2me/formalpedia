-- Prove2me | solution 1 for ErdosStraus242.family_mod319
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:44:41.580994+00:00
-- url     : https://prove2.me/submissions/8f5eb0bf-e056-4e0b-9546-8680eca75379

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 319 ∈ ({315, 311, 303, 299, 287, 279, 255, 239, 159} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 319
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 319 * k + n % 319 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h
  · -- class 315: alpha = 80, g = 1, beta = 79
    have hnform : n = 319 * k + 315 := by omega
    rw [hnform]
    refine ⟨80 * k + 79, 80 * (319 * k + 315), 80 * (80 * k + 79) * (319 * k + 315), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 80 * k + 79 := by nlinarith
      have hk2 : (0 : ℚ) < 319 * k + 315 := by nlinarith
      field_simp
      ring
  · -- class 311: alpha = 80, g = 2, beta = 78
    have hnform : n = 319 * k + 311 := by omega
    rw [hnform]
    refine ⟨80 * k + 78, 80 * (319 * k + 311), 40 * (80 * k + 78) * (319 * k + 311), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 80 * k + 78 := by nlinarith
      have hk2 : (0 : ℚ) < 319 * k + 311 := by nlinarith
      field_simp
      ring
  · -- class 303: alpha = 80, g = 4, beta = 76
    have hnform : n = 319 * k + 303 := by omega
    rw [hnform]
    refine ⟨80 * k + 76, 80 * (319 * k + 303), 20 * (80 * k + 76) * (319 * k + 303), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 80 * k + 76 := by nlinarith
      have hk2 : (0 : ℚ) < 319 * k + 303 := by nlinarith
      field_simp
      ring
  · -- class 299: alpha = 80, g = 5, beta = 75
    have hnform : n = 319 * k + 299 := by omega
    rw [hnform]
    refine ⟨80 * k + 75, 80 * (319 * k + 299), 16 * (80 * k + 75) * (319 * k + 299), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 80 * k + 75 := by nlinarith
      have hk2 : (0 : ℚ) < 319 * k + 299 := by nlinarith
      field_simp
      ring
  · -- class 287: alpha = 80, g = 8, beta = 72
    have hnform : n = 319 * k + 287 := by omega
    rw [hnform]
    refine ⟨80 * k + 72, 80 * (319 * k + 287), 10 * (80 * k + 72) * (319 * k + 287), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 80 * k + 72 := by nlinarith
      have hk2 : (0 : ℚ) < 319 * k + 287 := by nlinarith
      field_simp
      ring
  · -- class 279: alpha = 80, g = 10, beta = 70
    have hnform : n = 319 * k + 279 := by omega
    rw [hnform]
    refine ⟨80 * k + 70, 80 * (319 * k + 279), 8 * (80 * k + 70) * (319 * k + 279), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 80 * k + 70 := by nlinarith
      have hk2 : (0 : ℚ) < 319 * k + 279 := by nlinarith
      field_simp
      ring
  · -- class 255: alpha = 80, g = 16, beta = 64
    have hnform : n = 319 * k + 255 := by omega
    rw [hnform]
    refine ⟨80 * k + 64, 80 * (319 * k + 255), 5 * (80 * k + 64) * (319 * k + 255), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 80 * k + 64 := by nlinarith
      have hk2 : (0 : ℚ) < 319 * k + 255 := by nlinarith
      field_simp
      ring
  · -- class 239: alpha = 80, g = 20, beta = 60
    have hnform : n = 319 * k + 239 := by omega
    rw [hnform]
    refine ⟨80 * k + 60, 80 * (319 * k + 239), 4 * (80 * k + 60) * (319 * k + 239), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 80 * k + 60 := by nlinarith
      have hk2 : (0 : ℚ) < 319 * k + 239 := by nlinarith
      field_simp
      ring
  · -- class 159: alpha = 80, g = 40, beta = 40
    have hnform : n = 319 * k + 159 := by omega
    by_cases hk0 : k = 0
    · have h159 : n = 159 := by omega
      rw [h159]
      refine ⟨40, 6361, 40455960, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨80 * k + 40, 80 * (319 * k + 159), 2 * (80 * k + 40) * (319 * k + 159), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 80 * k + 40 := by nlinarith
        have hk2 : (0 : ℚ) < 319 * k + 159 := by nlinarith
        field_simp
        ring
