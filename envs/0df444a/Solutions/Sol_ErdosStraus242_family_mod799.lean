-- Prove2me | solution 1 for ErdosStraus242.family_mod799
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:30.531146+00:00
-- url     : https://prove2.me/submissions/ba936cb3-99fd-415a-86d0-b99b05e7f3e4

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 799 ∈ ({795, 791, 783, 779, 767, 759, 719, 699, 639, 599, 399} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 799
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 799 * k + n % 799 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h
  · -- class 795: alpha = 200, g = 1, beta = 199
    have hnform : n = 799 * k + 795 := by omega
    rw [hnform]
    refine ⟨200 * k + 199, 200 * (799 * k + 795), 200 * (200 * k + 199) * (799 * k + 795), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 200 * k + 199 := by nlinarith
      have hk2 : (0 : ℚ) < 799 * k + 795 := by nlinarith
      field_simp
      ring
  · -- class 791: alpha = 200, g = 2, beta = 198
    have hnform : n = 799 * k + 791 := by omega
    rw [hnform]
    refine ⟨200 * k + 198, 200 * (799 * k + 791), 100 * (200 * k + 198) * (799 * k + 791), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 200 * k + 198 := by nlinarith
      have hk2 : (0 : ℚ) < 799 * k + 791 := by nlinarith
      field_simp
      ring
  · -- class 783: alpha = 200, g = 4, beta = 196
    have hnform : n = 799 * k + 783 := by omega
    rw [hnform]
    refine ⟨200 * k + 196, 200 * (799 * k + 783), 50 * (200 * k + 196) * (799 * k + 783), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 200 * k + 196 := by nlinarith
      have hk2 : (0 : ℚ) < 799 * k + 783 := by nlinarith
      field_simp
      ring
  · -- class 779: alpha = 200, g = 5, beta = 195
    have hnform : n = 799 * k + 779 := by omega
    rw [hnform]
    refine ⟨200 * k + 195, 200 * (799 * k + 779), 40 * (200 * k + 195) * (799 * k + 779), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 200 * k + 195 := by nlinarith
      have hk2 : (0 : ℚ) < 799 * k + 779 := by nlinarith
      field_simp
      ring
  · -- class 767: alpha = 200, g = 8, beta = 192
    have hnform : n = 799 * k + 767 := by omega
    rw [hnform]
    refine ⟨200 * k + 192, 200 * (799 * k + 767), 25 * (200 * k + 192) * (799 * k + 767), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 200 * k + 192 := by nlinarith
      have hk2 : (0 : ℚ) < 799 * k + 767 := by nlinarith
      field_simp
      ring
  · -- class 759: alpha = 200, g = 10, beta = 190
    have hnform : n = 799 * k + 759 := by omega
    rw [hnform]
    refine ⟨200 * k + 190, 200 * (799 * k + 759), 20 * (200 * k + 190) * (799 * k + 759), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 200 * k + 190 := by nlinarith
      have hk2 : (0 : ℚ) < 799 * k + 759 := by nlinarith
      field_simp
      ring
  · -- class 719: alpha = 200, g = 20, beta = 180
    have hnform : n = 799 * k + 719 := by omega
    rw [hnform]
    refine ⟨200 * k + 180, 200 * (799 * k + 719), 10 * (200 * k + 180) * (799 * k + 719), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 200 * k + 180 := by nlinarith
      have hk2 : (0 : ℚ) < 799 * k + 719 := by nlinarith
      field_simp
      ring
  · -- class 699: alpha = 200, g = 25, beta = 175
    have hnform : n = 799 * k + 699 := by omega
    rw [hnform]
    refine ⟨200 * k + 175, 200 * (799 * k + 699), 8 * (200 * k + 175) * (799 * k + 699), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 200 * k + 175 := by nlinarith
      have hk2 : (0 : ℚ) < 799 * k + 699 := by nlinarith
      field_simp
      ring
  · -- class 639: alpha = 200, g = 40, beta = 160
    have hnform : n = 799 * k + 639 := by omega
    rw [hnform]
    refine ⟨200 * k + 160, 200 * (799 * k + 639), 5 * (200 * k + 160) * (799 * k + 639), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 200 * k + 160 := by nlinarith
      have hk2 : (0 : ℚ) < 799 * k + 639 := by nlinarith
      field_simp
      ring
  · -- class 599: alpha = 200, g = 50, beta = 150
    have hnform : n = 799 * k + 599 := by omega
    rw [hnform]
    refine ⟨200 * k + 150, 200 * (799 * k + 599), 4 * (200 * k + 150) * (799 * k + 599), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 200 * k + 150 := by nlinarith
      have hk2 : (0 : ℚ) < 799 * k + 599 := by nlinarith
      field_simp
      ring
  · -- class 399: alpha = 200, g = 100, beta = 100
    have hnform : n = 799 * k + 399 := by omega
    by_cases hk0 : k = 0
    · have h399 : n = 399 := by omega
      rw [h399]
      refine ⟨100, 39901, 1592049900, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨200 * k + 100, 200 * (799 * k + 399), 2 * (200 * k + 100) * (799 * k + 399), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 200 * k + 100 := by nlinarith
        have hk2 : (0 : ℚ) < 799 * k + 399 := by nlinarith
        field_simp
        ring
