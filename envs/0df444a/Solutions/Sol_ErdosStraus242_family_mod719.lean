-- Prove2me | solution 1 for ErdosStraus242.family_mod719
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:24.141737+00:00
-- url     : https://prove2.me/submissions/b1e23fa8-1f57-4752-85ff-ded8754c2c84

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 719 ∈ ({715, 711, 707, 703, 699, 695, 683, 679, 671, 659, 647, 639, 599, 575, 539, 479, 359} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 719
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 719 * k + n % 719 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · -- class 715: alpha = 180, g = 1, beta = 179
    have hnform : n = 719 * k + 715 := by omega
    rw [hnform]
    refine ⟨180 * k + 179, 180 * (719 * k + 715), 180 * (180 * k + 179) * (719 * k + 715), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 179 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 715 := by nlinarith
      field_simp
      ring
  · -- class 711: alpha = 180, g = 2, beta = 178
    have hnform : n = 719 * k + 711 := by omega
    rw [hnform]
    refine ⟨180 * k + 178, 180 * (719 * k + 711), 90 * (180 * k + 178) * (719 * k + 711), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 178 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 711 := by nlinarith
      field_simp
      ring
  · -- class 707: alpha = 180, g = 3, beta = 177
    have hnform : n = 719 * k + 707 := by omega
    rw [hnform]
    refine ⟨180 * k + 177, 180 * (719 * k + 707), 60 * (180 * k + 177) * (719 * k + 707), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 177 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 707 := by nlinarith
      field_simp
      ring
  · -- class 703: alpha = 180, g = 4, beta = 176
    have hnform : n = 719 * k + 703 := by omega
    rw [hnform]
    refine ⟨180 * k + 176, 180 * (719 * k + 703), 45 * (180 * k + 176) * (719 * k + 703), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 176 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 703 := by nlinarith
      field_simp
      ring
  · -- class 699: alpha = 180, g = 5, beta = 175
    have hnform : n = 719 * k + 699 := by omega
    rw [hnform]
    refine ⟨180 * k + 175, 180 * (719 * k + 699), 36 * (180 * k + 175) * (719 * k + 699), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 175 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 699 := by nlinarith
      field_simp
      ring
  · -- class 695: alpha = 180, g = 6, beta = 174
    have hnform : n = 719 * k + 695 := by omega
    rw [hnform]
    refine ⟨180 * k + 174, 180 * (719 * k + 695), 30 * (180 * k + 174) * (719 * k + 695), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 174 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 695 := by nlinarith
      field_simp
      ring
  · -- class 683: alpha = 180, g = 9, beta = 171
    have hnform : n = 719 * k + 683 := by omega
    rw [hnform]
    refine ⟨180 * k + 171, 180 * (719 * k + 683), 20 * (180 * k + 171) * (719 * k + 683), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 171 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 683 := by nlinarith
      field_simp
      ring
  · -- class 679: alpha = 180, g = 10, beta = 170
    have hnform : n = 719 * k + 679 := by omega
    rw [hnform]
    refine ⟨180 * k + 170, 180 * (719 * k + 679), 18 * (180 * k + 170) * (719 * k + 679), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 170 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 679 := by nlinarith
      field_simp
      ring
  · -- class 671: alpha = 180, g = 12, beta = 168
    have hnform : n = 719 * k + 671 := by omega
    rw [hnform]
    refine ⟨180 * k + 168, 180 * (719 * k + 671), 15 * (180 * k + 168) * (719 * k + 671), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 168 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 671 := by nlinarith
      field_simp
      ring
  · -- class 659: alpha = 180, g = 15, beta = 165
    have hnform : n = 719 * k + 659 := by omega
    rw [hnform]
    refine ⟨180 * k + 165, 180 * (719 * k + 659), 12 * (180 * k + 165) * (719 * k + 659), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 165 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 659 := by nlinarith
      field_simp
      ring
  · -- class 647: alpha = 180, g = 18, beta = 162
    have hnform : n = 719 * k + 647 := by omega
    rw [hnform]
    refine ⟨180 * k + 162, 180 * (719 * k + 647), 10 * (180 * k + 162) * (719 * k + 647), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 162 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 647 := by nlinarith
      field_simp
      ring
  · -- class 639: alpha = 180, g = 20, beta = 160
    have hnform : n = 719 * k + 639 := by omega
    rw [hnform]
    refine ⟨180 * k + 160, 180 * (719 * k + 639), 9 * (180 * k + 160) * (719 * k + 639), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 160 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 639 := by nlinarith
      field_simp
      ring
  · -- class 599: alpha = 180, g = 30, beta = 150
    have hnform : n = 719 * k + 599 := by omega
    rw [hnform]
    refine ⟨180 * k + 150, 180 * (719 * k + 599), 6 * (180 * k + 150) * (719 * k + 599), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 150 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 599 := by nlinarith
      field_simp
      ring
  · -- class 575: alpha = 180, g = 36, beta = 144
    have hnform : n = 719 * k + 575 := by omega
    rw [hnform]
    refine ⟨180 * k + 144, 180 * (719 * k + 575), 5 * (180 * k + 144) * (719 * k + 575), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 144 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 575 := by nlinarith
      field_simp
      ring
  · -- class 539: alpha = 180, g = 45, beta = 135
    have hnform : n = 719 * k + 539 := by omega
    rw [hnform]
    refine ⟨180 * k + 135, 180 * (719 * k + 539), 4 * (180 * k + 135) * (719 * k + 539), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 135 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 539 := by nlinarith
      field_simp
      ring
  · -- class 479: alpha = 180, g = 60, beta = 120
    have hnform : n = 719 * k + 479 := by omega
    rw [hnform]
    refine ⟨180 * k + 120, 180 * (719 * k + 479), 3 * (180 * k + 120) * (719 * k + 479), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 180 * k + 120 := by nlinarith
      have hk2 : (0 : ℚ) < 719 * k + 479 := by nlinarith
      field_simp
      ring
  · -- class 359: alpha = 180, g = 90, beta = 90
    have hnform : n = 719 * k + 359 := by omega
    by_cases hk0 : k = 0
    · have h359 : n = 359 := by omega
      rw [h359]
      refine ⟨90, 32311, 1043968410, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨180 * k + 90, 180 * (719 * k + 359), 2 * (180 * k + 90) * (719 * k + 359), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 180 * k + 90 := by nlinarith
        have hk2 : (0 : ℚ) < 719 * k + 359 := by nlinarith
        field_simp
        ring
