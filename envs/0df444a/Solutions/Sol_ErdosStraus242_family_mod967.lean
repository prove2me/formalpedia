-- Prove2me | solution 1 for ErdosStraus242.family_mod967
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:13:05.847608+00:00
-- url     : https://prove2.me/submissions/57fc96f7-c7fc-4c1c-8fb2-0342d004264e

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 967 ∈ ({963, 959, 923, 879, 483} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 967
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 967 * k + n % 967 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h
  · -- class 963: alpha = 242, g = 1, beta = 241
    have hnform : n = 967 * k + 963 := by omega
    rw [hnform]
    refine ⟨242 * k + 241, 242 * (967 * k + 963), 242 * (242 * k + 241) * (967 * k + 963), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 242 * k + 241 := by nlinarith
      have hk2 : (0 : ℚ) < 967 * k + 963 := by nlinarith
      field_simp
      ring
  · -- class 959: alpha = 242, g = 2, beta = 240
    have hnform : n = 967 * k + 959 := by omega
    rw [hnform]
    refine ⟨242 * k + 240, 242 * (967 * k + 959), 121 * (242 * k + 240) * (967 * k + 959), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 242 * k + 240 := by nlinarith
      have hk2 : (0 : ℚ) < 967 * k + 959 := by nlinarith
      field_simp
      ring
  · -- class 923: alpha = 242, g = 11, beta = 231
    have hnform : n = 967 * k + 923 := by omega
    rw [hnform]
    refine ⟨242 * k + 231, 242 * (967 * k + 923), 22 * (242 * k + 231) * (967 * k + 923), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 242 * k + 231 := by nlinarith
      have hk2 : (0 : ℚ) < 967 * k + 923 := by nlinarith
      field_simp
      ring
  · -- class 879: alpha = 242, g = 22, beta = 220
    have hnform : n = 967 * k + 879 := by omega
    rw [hnform]
    refine ⟨242 * k + 220, 242 * (967 * k + 879), 11 * (242 * k + 220) * (967 * k + 879), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 242 * k + 220 := by nlinarith
      have hk2 : (0 : ℚ) < 967 * k + 879 := by nlinarith
      field_simp
      ring
  · -- class 483: alpha = 242, g = 121, beta = 121
    have hnform : n = 967 * k + 483 := by omega
    by_cases hk0 : k = 0
    · have h483 : n = 483 := by omega
      rw [h483]
      refine ⟨121, 58444, 3415642692, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨242 * k + 121, 242 * (967 * k + 483), 2 * (242 * k + 121) * (967 * k + 483), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 242 * k + 121 := by nlinarith
        have hk2 : (0 : ℚ) < 967 * k + 483 := by nlinarith
        field_simp
        ring
