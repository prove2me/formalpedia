-- Prove2me | solution 2 for ErdosStraus242.family_mod647
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:20.628614+00:00
-- url     : https://prove2.me/submissions/fda79f91-57a0-4d85-9db9-a8aca5aaddc5

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 647 ∈ ({643, 639, 635, 623, 611, 575, 539, 431, 323} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 647
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 647 * k + n % 647 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h
  · -- class 643: alpha = 162, g = 1, beta = 161
    have hnform : n = 647 * k + 643 := by omega
    rw [hnform]
    refine ⟨162 * k + 161, 162 * (647 * k + 643), 162 * (162 * k + 161) * (647 * k + 643), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 162 * k + 161 := by nlinarith
      have hk2 : (0 : ℚ) < 647 * k + 643 := by nlinarith
      field_simp
      ring
  · -- class 639: alpha = 162, g = 2, beta = 160
    have hnform : n = 647 * k + 639 := by omega
    rw [hnform]
    refine ⟨162 * k + 160, 162 * (647 * k + 639), 81 * (162 * k + 160) * (647 * k + 639), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 162 * k + 160 := by nlinarith
      have hk2 : (0 : ℚ) < 647 * k + 639 := by nlinarith
      field_simp
      ring
  · -- class 635: alpha = 162, g = 3, beta = 159
    have hnform : n = 647 * k + 635 := by omega
    rw [hnform]
    refine ⟨162 * k + 159, 162 * (647 * k + 635), 54 * (162 * k + 159) * (647 * k + 635), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 162 * k + 159 := by nlinarith
      have hk2 : (0 : ℚ) < 647 * k + 635 := by nlinarith
      field_simp
      ring
  · -- class 623: alpha = 162, g = 6, beta = 156
    have hnform : n = 647 * k + 623 := by omega
    rw [hnform]
    refine ⟨162 * k + 156, 162 * (647 * k + 623), 27 * (162 * k + 156) * (647 * k + 623), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 162 * k + 156 := by nlinarith
      have hk2 : (0 : ℚ) < 647 * k + 623 := by nlinarith
      field_simp
      ring
  · -- class 611: alpha = 162, g = 9, beta = 153
    have hnform : n = 647 * k + 611 := by omega
    rw [hnform]
    refine ⟨162 * k + 153, 162 * (647 * k + 611), 18 * (162 * k + 153) * (647 * k + 611), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 162 * k + 153 := by nlinarith
      have hk2 : (0 : ℚ) < 647 * k + 611 := by nlinarith
      field_simp
      ring
  · -- class 575: alpha = 162, g = 18, beta = 144
    have hnform : n = 647 * k + 575 := by omega
    rw [hnform]
    refine ⟨162 * k + 144, 162 * (647 * k + 575), 9 * (162 * k + 144) * (647 * k + 575), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 162 * k + 144 := by nlinarith
      have hk2 : (0 : ℚ) < 647 * k + 575 := by nlinarith
      field_simp
      ring
  · -- class 539: alpha = 162, g = 27, beta = 135
    have hnform : n = 647 * k + 539 := by omega
    rw [hnform]
    refine ⟨162 * k + 135, 162 * (647 * k + 539), 6 * (162 * k + 135) * (647 * k + 539), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 162 * k + 135 := by nlinarith
      have hk2 : (0 : ℚ) < 647 * k + 539 := by nlinarith
      field_simp
      ring
  · -- class 431: alpha = 162, g = 54, beta = 108
    have hnform : n = 647 * k + 431 := by omega
    rw [hnform]
    refine ⟨162 * k + 108, 162 * (647 * k + 431), 3 * (162 * k + 108) * (647 * k + 431), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 162 * k + 108 := by nlinarith
      have hk2 : (0 : ℚ) < 647 * k + 431 := by nlinarith
      field_simp
      ring
  · -- class 323: alpha = 162, g = 81, beta = 81
    have hnform : n = 647 * k + 323 := by omega
    by_cases hk0 : k = 0
    · have h323 : n = 323 := by omega
      rw [h323]
      refine ⟨81, 26164, 684528732, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨162 * k + 81, 162 * (647 * k + 323), 2 * (162 * k + 81) * (647 * k + 323), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 162 * k + 81 := by nlinarith
        have hk2 : (0 : ℚ) < 647 * k + 323 := by nlinarith
        field_simp
        ring
