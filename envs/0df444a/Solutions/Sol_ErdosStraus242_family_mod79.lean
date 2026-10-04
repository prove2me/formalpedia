-- Prove2me | solution 1 for ErdosStraus242.family_mod79
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:16:33.274082+00:00
-- url     : https://prove2.me/submissions/bb1ea1e8-27d9-4e3b-bc0c-0d0e4e477a5c

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 79 ∈ ({39, 59, 63, 71, 75} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 79
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 79 * k + n % 79 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h
  · -- class 39: alpha = 20, g = 10, beta = 10
    have hnform : n = 79 * k + 39 := by omega
    by_cases hk0 : k = 0
    · have h39 : n = 39 := by omega
      rw [h39]
      refine ⟨14, 52, 84, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · rw [hnform]
      have hk1 : 1 ≤ k := by omega
      refine ⟨20 * k + 10, 20 * (79 * k + 39), 2 * (20 * k + 10) * (79 * k + 39), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 20 * k + 10 := by nlinarith
        have hk2 : (0 : ℚ) < 79 * k + 39 := by nlinarith
        field_simp
        ring
  · -- class 59: alpha = 20, g = 5, beta = 15
    have hnform : n = 79 * k + 59 := by omega
    rw [hnform]
    refine ⟨20 * k + 15, 20 * (79 * k + 59), 4 * (20 * k + 15) * (79 * k + 59), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 20 * k + 15 := by nlinarith
      have hk2 : (0 : ℚ) < 79 * k + 59 := by nlinarith
      field_simp
      ring
  · -- class 63: alpha = 20, g = 4, beta = 16
    have hnform : n = 79 * k + 63 := by omega
    rw [hnform]
    refine ⟨20 * k + 16, 20 * (79 * k + 63), 5 * (20 * k + 16) * (79 * k + 63), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 20 * k + 16 := by nlinarith
      have hk2 : (0 : ℚ) < 79 * k + 63 := by nlinarith
      field_simp
      ring
  · -- class 71: alpha = 20, g = 2, beta = 18
    have hnform : n = 79 * k + 71 := by omega
    rw [hnform]
    refine ⟨20 * k + 18, 20 * (79 * k + 71), 10 * (20 * k + 18) * (79 * k + 71), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 20 * k + 18 := by nlinarith
      have hk2 : (0 : ℚ) < 79 * k + 71 := by nlinarith
      field_simp
      ring
  · -- class 75: alpha = 20, g = 1, beta = 19
    have hnform : n = 79 * k + 75 := by omega
    rw [hnform]
    refine ⟨20 * k + 19, 20 * (79 * k + 75), 20 * (20 * k + 19) * (79 * k + 75), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 20 * k + 19 := by nlinarith
      have hk2 : (0 : ℚ) < 79 * k + 75 := by nlinarith
      field_simp
      ring
