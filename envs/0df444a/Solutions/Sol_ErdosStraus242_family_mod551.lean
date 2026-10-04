-- Prove2me | solution 1 for ErdosStraus242.family_mod551
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:37.49679+00:00
-- url     : https://prove2.me/submissions/cc7da557-4087-4709-aa77-e18e05a260a9

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 551 ∈ ({547, 543, 539, 527, 459, 367, 275} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 551
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 551 * k + n % 551 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 547: alpha = 138, g = 1, beta = 137
    have hnform : n = 551 * k + 547 := by omega
    rw [hnform]
    refine ⟨138 * k + 137, 138 * (551 * k + 547), 138 * (138 * k + 137) * (551 * k + 547), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 138 * k + 137 := by nlinarith
      have hk2 : (0 : ℚ) < 551 * k + 547 := by nlinarith
      field_simp
      ring
  · -- class 543: alpha = 138, g = 2, beta = 136
    have hnform : n = 551 * k + 543 := by omega
    rw [hnform]
    refine ⟨138 * k + 136, 138 * (551 * k + 543), 69 * (138 * k + 136) * (551 * k + 543), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 138 * k + 136 := by nlinarith
      have hk2 : (0 : ℚ) < 551 * k + 543 := by nlinarith
      field_simp
      ring
  · -- class 539: alpha = 138, g = 3, beta = 135
    have hnform : n = 551 * k + 539 := by omega
    rw [hnform]
    refine ⟨138 * k + 135, 138 * (551 * k + 539), 46 * (138 * k + 135) * (551 * k + 539), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 138 * k + 135 := by nlinarith
      have hk2 : (0 : ℚ) < 551 * k + 539 := by nlinarith
      field_simp
      ring
  · -- class 527: alpha = 138, g = 6, beta = 132
    have hnform : n = 551 * k + 527 := by omega
    rw [hnform]
    refine ⟨138 * k + 132, 138 * (551 * k + 527), 23 * (138 * k + 132) * (551 * k + 527), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 138 * k + 132 := by nlinarith
      have hk2 : (0 : ℚ) < 551 * k + 527 := by nlinarith
      field_simp
      ring
  · -- class 459: alpha = 138, g = 23, beta = 115
    have hnform : n = 551 * k + 459 := by omega
    rw [hnform]
    refine ⟨138 * k + 115, 138 * (551 * k + 459), 6 * (138 * k + 115) * (551 * k + 459), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 138 * k + 115 := by nlinarith
      have hk2 : (0 : ℚ) < 551 * k + 459 := by nlinarith
      field_simp
      ring
  · -- class 367: alpha = 138, g = 46, beta = 92
    have hnform : n = 551 * k + 367 := by omega
    rw [hnform]
    refine ⟨138 * k + 92, 138 * (551 * k + 367), 3 * (138 * k + 92) * (551 * k + 367), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 138 * k + 92 := by nlinarith
      have hk2 : (0 : ℚ) < 551 * k + 367 := by nlinarith
      field_simp
      ring
  · -- class 275: alpha = 138, g = 69, beta = 69
    have hnform : n = 551 * k + 275 := by omega
    by_cases hk0 : k = 0
    · have h275 : n = 275 := by omega
      rw [h275]
      refine ⟨69, 18976, 360069600, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨138 * k + 69, 138 * (551 * k + 275), 2 * (138 * k + 69) * (551 * k + 275), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 138 * k + 69 := by nlinarith
        have hk2 : (0 : ℚ) < 551 * k + 275 := by nlinarith
        field_simp
        ring
