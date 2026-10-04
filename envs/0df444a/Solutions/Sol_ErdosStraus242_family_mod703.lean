-- Prove2me | solution 1 for ErdosStraus242.family_mod703
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:23.705446+00:00
-- url     : https://prove2.me/submissions/17c3df03-3b86-4927-845b-6d80c0fb953f

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 703 ∈ ({699, 695, 687, 671, 659, 639, 615, 527, 351} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 703
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 703 * k + n % 703 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h
  · -- class 699: alpha = 176, g = 1, beta = 175
    have hnform : n = 703 * k + 699 := by omega
    rw [hnform]
    refine ⟨176 * k + 175, 176 * (703 * k + 699), 176 * (176 * k + 175) * (703 * k + 699), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 176 * k + 175 := by nlinarith
      have hk2 : (0 : ℚ) < 703 * k + 699 := by nlinarith
      field_simp
      ring
  · -- class 695: alpha = 176, g = 2, beta = 174
    have hnform : n = 703 * k + 695 := by omega
    rw [hnform]
    refine ⟨176 * k + 174, 176 * (703 * k + 695), 88 * (176 * k + 174) * (703 * k + 695), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 176 * k + 174 := by nlinarith
      have hk2 : (0 : ℚ) < 703 * k + 695 := by nlinarith
      field_simp
      ring
  · -- class 687: alpha = 176, g = 4, beta = 172
    have hnform : n = 703 * k + 687 := by omega
    rw [hnform]
    refine ⟨176 * k + 172, 176 * (703 * k + 687), 44 * (176 * k + 172) * (703 * k + 687), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 176 * k + 172 := by nlinarith
      have hk2 : (0 : ℚ) < 703 * k + 687 := by nlinarith
      field_simp
      ring
  · -- class 671: alpha = 176, g = 8, beta = 168
    have hnform : n = 703 * k + 671 := by omega
    rw [hnform]
    refine ⟨176 * k + 168, 176 * (703 * k + 671), 22 * (176 * k + 168) * (703 * k + 671), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 176 * k + 168 := by nlinarith
      have hk2 : (0 : ℚ) < 703 * k + 671 := by nlinarith
      field_simp
      ring
  · -- class 659: alpha = 176, g = 11, beta = 165
    have hnform : n = 703 * k + 659 := by omega
    rw [hnform]
    refine ⟨176 * k + 165, 176 * (703 * k + 659), 16 * (176 * k + 165) * (703 * k + 659), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 176 * k + 165 := by nlinarith
      have hk2 : (0 : ℚ) < 703 * k + 659 := by nlinarith
      field_simp
      ring
  · -- class 639: alpha = 176, g = 16, beta = 160
    have hnform : n = 703 * k + 639 := by omega
    rw [hnform]
    refine ⟨176 * k + 160, 176 * (703 * k + 639), 11 * (176 * k + 160) * (703 * k + 639), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 176 * k + 160 := by nlinarith
      have hk2 : (0 : ℚ) < 703 * k + 639 := by nlinarith
      field_simp
      ring
  · -- class 615: alpha = 176, g = 22, beta = 154
    have hnform : n = 703 * k + 615 := by omega
    rw [hnform]
    refine ⟨176 * k + 154, 176 * (703 * k + 615), 8 * (176 * k + 154) * (703 * k + 615), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 176 * k + 154 := by nlinarith
      have hk2 : (0 : ℚ) < 703 * k + 615 := by nlinarith
      field_simp
      ring
  · -- class 527: alpha = 176, g = 44, beta = 132
    have hnform : n = 703 * k + 527 := by omega
    rw [hnform]
    refine ⟨176 * k + 132, 176 * (703 * k + 527), 4 * (176 * k + 132) * (703 * k + 527), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 176 * k + 132 := by nlinarith
      have hk2 : (0 : ℚ) < 703 * k + 527 := by nlinarith
      field_simp
      ring
  · -- class 351: alpha = 176, g = 88, beta = 88
    have hnform : n = 703 * k + 351 := by omega
    by_cases hk0 : k = 0
    · have h351 : n = 351 := by omega
      rw [h351]
      refine ⟨88, 30889, 954099432, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨176 * k + 88, 176 * (703 * k + 351), 2 * (176 * k + 88) * (703 * k + 351), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 176 * k + 88 := by nlinarith
        have hk2 : (0 : ℚ) < 703 * k + 351 := by nlinarith
        field_simp
        ring
