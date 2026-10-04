-- Prove2me | solution 1 for ErdosStraus242.family_mod463
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:33.59685+00:00
-- url     : https://prove2.me/submissions/4181d755-9187-41ce-ad98-a3b46aa54398

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 463 ∈ ({459, 455, 447, 347, 231} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 463
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 463 * k + n % 463 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h
  · -- class 459: alpha = 116, g = 1, beta = 115
    have hnform : n = 463 * k + 459 := by omega
    rw [hnform]
    refine ⟨116 * k + 115, 116 * (463 * k + 459), 116 * (116 * k + 115) * (463 * k + 459), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 116 * k + 115 := by nlinarith
      have hk2 : (0 : ℚ) < 463 * k + 459 := by nlinarith
      field_simp
      ring
  · -- class 455: alpha = 116, g = 2, beta = 114
    have hnform : n = 463 * k + 455 := by omega
    rw [hnform]
    refine ⟨116 * k + 114, 116 * (463 * k + 455), 58 * (116 * k + 114) * (463 * k + 455), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 116 * k + 114 := by nlinarith
      have hk2 : (0 : ℚ) < 463 * k + 455 := by nlinarith
      field_simp
      ring
  · -- class 447: alpha = 116, g = 4, beta = 112
    have hnform : n = 463 * k + 447 := by omega
    rw [hnform]
    refine ⟨116 * k + 112, 116 * (463 * k + 447), 29 * (116 * k + 112) * (463 * k + 447), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 116 * k + 112 := by nlinarith
      have hk2 : (0 : ℚ) < 463 * k + 447 := by nlinarith
      field_simp
      ring
  · -- class 347: alpha = 116, g = 29, beta = 87
    have hnform : n = 463 * k + 347 := by omega
    rw [hnform]
    refine ⟨116 * k + 87, 116 * (463 * k + 347), 4 * (116 * k + 87) * (463 * k + 347), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 116 * k + 87 := by nlinarith
      have hk2 : (0 : ℚ) < 463 * k + 347 := by nlinarith
      field_simp
      ring
  · -- class 231: alpha = 116, g = 58, beta = 58
    have hnform : n = 463 * k + 231 := by omega
    by_cases hk0 : k = 0
    · have h231 : n = 231 := by omega
      rw [h231]
      refine ⟨58, 13399, 179519802, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨116 * k + 58, 116 * (463 * k + 231), 2 * (116 * k + 58) * (463 * k + 231), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 116 * k + 58 := by nlinarith
        have hk2 : (0 : ℚ) < 463 * k + 231 := by nlinarith
        field_simp
        ring
