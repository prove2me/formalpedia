-- Prove2me | solution 1 for ErdosStraus242.family_mod727
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:24.711633+00:00
-- url     : https://prove2.me/submissions/a65fadac-79e5-4abf-adc3-eff4ec16b0f4

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 727 ∈ ({723, 719, 699, 675, 671, 623, 363} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 727
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 727 * k + n % 727 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 723: alpha = 182, g = 1, beta = 181
    have hnform : n = 727 * k + 723 := by omega
    rw [hnform]
    refine ⟨182 * k + 181, 182 * (727 * k + 723), 182 * (182 * k + 181) * (727 * k + 723), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 182 * k + 181 := by nlinarith
      have hk2 : (0 : ℚ) < 727 * k + 723 := by nlinarith
      field_simp
      ring
  · -- class 719: alpha = 182, g = 2, beta = 180
    have hnform : n = 727 * k + 719 := by omega
    rw [hnform]
    refine ⟨182 * k + 180, 182 * (727 * k + 719), 91 * (182 * k + 180) * (727 * k + 719), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 182 * k + 180 := by nlinarith
      have hk2 : (0 : ℚ) < 727 * k + 719 := by nlinarith
      field_simp
      ring
  · -- class 699: alpha = 182, g = 7, beta = 175
    have hnform : n = 727 * k + 699 := by omega
    rw [hnform]
    refine ⟨182 * k + 175, 182 * (727 * k + 699), 26 * (182 * k + 175) * (727 * k + 699), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 182 * k + 175 := by nlinarith
      have hk2 : (0 : ℚ) < 727 * k + 699 := by nlinarith
      field_simp
      ring
  · -- class 675: alpha = 182, g = 13, beta = 169
    have hnform : n = 727 * k + 675 := by omega
    rw [hnform]
    refine ⟨182 * k + 169, 182 * (727 * k + 675), 14 * (182 * k + 169) * (727 * k + 675), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 182 * k + 169 := by nlinarith
      have hk2 : (0 : ℚ) < 727 * k + 675 := by nlinarith
      field_simp
      ring
  · -- class 671: alpha = 182, g = 14, beta = 168
    have hnform : n = 727 * k + 671 := by omega
    rw [hnform]
    refine ⟨182 * k + 168, 182 * (727 * k + 671), 13 * (182 * k + 168) * (727 * k + 671), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 182 * k + 168 := by nlinarith
      have hk2 : (0 : ℚ) < 727 * k + 671 := by nlinarith
      field_simp
      ring
  · -- class 623: alpha = 182, g = 26, beta = 156
    have hnform : n = 727 * k + 623 := by omega
    rw [hnform]
    refine ⟨182 * k + 156, 182 * (727 * k + 623), 7 * (182 * k + 156) * (727 * k + 623), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 182 * k + 156 := by nlinarith
      have hk2 : (0 : ℚ) < 727 * k + 623 := by nlinarith
      field_simp
      ring
  · -- class 363: alpha = 182, g = 91, beta = 91
    have hnform : n = 727 * k + 363 := by omega
    by_cases hk0 : k = 0
    · have h363 : n = 363 := by omega
      rw [h363]
      refine ⟨91, 33034, 1091212122, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨182 * k + 91, 182 * (727 * k + 363), 2 * (182 * k + 91) * (727 * k + 363), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 182 * k + 91 := by nlinarith
        have hk2 : (0 : ℚ) < 727 * k + 363 := by nlinarith
        field_simp
        ring
