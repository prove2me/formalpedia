-- Prove2me | solution 1 for ErdosStraus242.family_mod919
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:13:03.420007+00:00
-- url     : https://prove2.me/submissions/de5aaccd-b745-4627-a6b3-3916f5ca49f9

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 919 ∈ ({915, 911, 899, 879, 827, 735, 459} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 919
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 919 * k + n % 919 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 915: alpha = 230, g = 1, beta = 229
    have hnform : n = 919 * k + 915 := by omega
    rw [hnform]
    refine ⟨230 * k + 229, 230 * (919 * k + 915), 230 * (230 * k + 229) * (919 * k + 915), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 230 * k + 229 := by nlinarith
      have hk2 : (0 : ℚ) < 919 * k + 915 := by nlinarith
      field_simp
      ring
  · -- class 911: alpha = 230, g = 2, beta = 228
    have hnform : n = 919 * k + 911 := by omega
    rw [hnform]
    refine ⟨230 * k + 228, 230 * (919 * k + 911), 115 * (230 * k + 228) * (919 * k + 911), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 230 * k + 228 := by nlinarith
      have hk2 : (0 : ℚ) < 919 * k + 911 := by nlinarith
      field_simp
      ring
  · -- class 899: alpha = 230, g = 5, beta = 225
    have hnform : n = 919 * k + 899 := by omega
    rw [hnform]
    refine ⟨230 * k + 225, 230 * (919 * k + 899), 46 * (230 * k + 225) * (919 * k + 899), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 230 * k + 225 := by nlinarith
      have hk2 : (0 : ℚ) < 919 * k + 899 := by nlinarith
      field_simp
      ring
  · -- class 879: alpha = 230, g = 10, beta = 220
    have hnform : n = 919 * k + 879 := by omega
    rw [hnform]
    refine ⟨230 * k + 220, 230 * (919 * k + 879), 23 * (230 * k + 220) * (919 * k + 879), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 230 * k + 220 := by nlinarith
      have hk2 : (0 : ℚ) < 919 * k + 879 := by nlinarith
      field_simp
      ring
  · -- class 827: alpha = 230, g = 23, beta = 207
    have hnform : n = 919 * k + 827 := by omega
    rw [hnform]
    refine ⟨230 * k + 207, 230 * (919 * k + 827), 10 * (230 * k + 207) * (919 * k + 827), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 230 * k + 207 := by nlinarith
      have hk2 : (0 : ℚ) < 919 * k + 827 := by nlinarith
      field_simp
      ring
  · -- class 735: alpha = 230, g = 46, beta = 184
    have hnform : n = 919 * k + 735 := by omega
    rw [hnform]
    refine ⟨230 * k + 184, 230 * (919 * k + 735), 5 * (230 * k + 184) * (919 * k + 735), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 230 * k + 184 := by nlinarith
      have hk2 : (0 : ℚ) < 919 * k + 735 := by nlinarith
      field_simp
      ring
  · -- class 459: alpha = 230, g = 115, beta = 115
    have hnform : n = 919 * k + 459 := by omega
    by_cases hk0 : k = 0
    · have h459 : n = 459 := by omega
      rw [h459]
      refine ⟨115, 52786, 2786309010, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨230 * k + 115, 230 * (919 * k + 459), 2 * (230 * k + 115) * (919 * k + 459), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 230 * k + 115 := by nlinarith
        have hk2 : (0 : ℚ) < 919 * k + 459 := by nlinarith
        field_simp
        ring
