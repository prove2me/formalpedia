-- Prove2me | solution 1 for ErdosStraus242.family_mod599
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:40.680835+00:00
-- url     : https://prove2.me/submissions/ee57ab58-4e45-4fa8-86fb-642ed317be73

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 599 ∈ ({595, 591, 587, 579, 575, 559, 539, 499, 479, 399, 299} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 599
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 599 * k + n % 599 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h
  · -- class 595: alpha = 150, g = 1, beta = 149
    have hnform : n = 599 * k + 595 := by omega
    rw [hnform]
    refine ⟨150 * k + 149, 150 * (599 * k + 595), 150 * (150 * k + 149) * (599 * k + 595), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 150 * k + 149 := by nlinarith
      have hk2 : (0 : ℚ) < 599 * k + 595 := by nlinarith
      field_simp
      ring
  · -- class 591: alpha = 150, g = 2, beta = 148
    have hnform : n = 599 * k + 591 := by omega
    rw [hnform]
    refine ⟨150 * k + 148, 150 * (599 * k + 591), 75 * (150 * k + 148) * (599 * k + 591), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 150 * k + 148 := by nlinarith
      have hk2 : (0 : ℚ) < 599 * k + 591 := by nlinarith
      field_simp
      ring
  · -- class 587: alpha = 150, g = 3, beta = 147
    have hnform : n = 599 * k + 587 := by omega
    rw [hnform]
    refine ⟨150 * k + 147, 150 * (599 * k + 587), 50 * (150 * k + 147) * (599 * k + 587), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 150 * k + 147 := by nlinarith
      have hk2 : (0 : ℚ) < 599 * k + 587 := by nlinarith
      field_simp
      ring
  · -- class 579: alpha = 150, g = 5, beta = 145
    have hnform : n = 599 * k + 579 := by omega
    rw [hnform]
    refine ⟨150 * k + 145, 150 * (599 * k + 579), 30 * (150 * k + 145) * (599 * k + 579), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 150 * k + 145 := by nlinarith
      have hk2 : (0 : ℚ) < 599 * k + 579 := by nlinarith
      field_simp
      ring
  · -- class 575: alpha = 150, g = 6, beta = 144
    have hnform : n = 599 * k + 575 := by omega
    rw [hnform]
    refine ⟨150 * k + 144, 150 * (599 * k + 575), 25 * (150 * k + 144) * (599 * k + 575), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 150 * k + 144 := by nlinarith
      have hk2 : (0 : ℚ) < 599 * k + 575 := by nlinarith
      field_simp
      ring
  · -- class 559: alpha = 150, g = 10, beta = 140
    have hnform : n = 599 * k + 559 := by omega
    rw [hnform]
    refine ⟨150 * k + 140, 150 * (599 * k + 559), 15 * (150 * k + 140) * (599 * k + 559), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 150 * k + 140 := by nlinarith
      have hk2 : (0 : ℚ) < 599 * k + 559 := by nlinarith
      field_simp
      ring
  · -- class 539: alpha = 150, g = 15, beta = 135
    have hnform : n = 599 * k + 539 := by omega
    rw [hnform]
    refine ⟨150 * k + 135, 150 * (599 * k + 539), 10 * (150 * k + 135) * (599 * k + 539), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 150 * k + 135 := by nlinarith
      have hk2 : (0 : ℚ) < 599 * k + 539 := by nlinarith
      field_simp
      ring
  · -- class 499: alpha = 150, g = 25, beta = 125
    have hnform : n = 599 * k + 499 := by omega
    rw [hnform]
    refine ⟨150 * k + 125, 150 * (599 * k + 499), 6 * (150 * k + 125) * (599 * k + 499), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 150 * k + 125 := by nlinarith
      have hk2 : (0 : ℚ) < 599 * k + 499 := by nlinarith
      field_simp
      ring
  · -- class 479: alpha = 150, g = 30, beta = 120
    have hnform : n = 599 * k + 479 := by omega
    rw [hnform]
    refine ⟨150 * k + 120, 150 * (599 * k + 479), 5 * (150 * k + 120) * (599 * k + 479), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 150 * k + 120 := by nlinarith
      have hk2 : (0 : ℚ) < 599 * k + 479 := by nlinarith
      field_simp
      ring
  · -- class 399: alpha = 150, g = 50, beta = 100
    have hnform : n = 599 * k + 399 := by omega
    rw [hnform]
    refine ⟨150 * k + 100, 150 * (599 * k + 399), 3 * (150 * k + 100) * (599 * k + 399), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 150 * k + 100 := by nlinarith
      have hk2 : (0 : ℚ) < 599 * k + 399 := by nlinarith
      field_simp
      ring
  · -- class 299: alpha = 150, g = 75, beta = 75
    have hnform : n = 599 * k + 299 := by omega
    by_cases hk0 : k = 0
    · have h299 : n = 299 := by omega
      rw [h299]
      refine ⟨75, 22426, 502903050, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨150 * k + 75, 150 * (599 * k + 299), 2 * (150 * k + 75) * (599 * k + 299), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 150 * k + 75 := by nlinarith
        have hk2 : (0 : ℚ) < 599 * k + 299 := by nlinarith
        field_simp
        ring
