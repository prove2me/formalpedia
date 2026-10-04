-- Prove2me | solution 1 for ErdosStraus242.family_mod839
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:33.44328+00:00
-- url     : https://prove2.me/submissions/62ca4001-66b6-43b1-8662-0bc319d6df24

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 839 ∈ ({835, 831, 827, 819, 815, 811, 799, 783, 779, 755, 719, 699, 671, 559, 419} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 839
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 839 * k + n % 839 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · -- class 835: alpha = 210, g = 1, beta = 209
    have hnform : n = 839 * k + 835 := by omega
    rw [hnform]
    refine ⟨210 * k + 209, 210 * (839 * k + 835), 210 * (210 * k + 209) * (839 * k + 835), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 210 * k + 209 := by nlinarith
      have hk2 : (0 : ℚ) < 839 * k + 835 := by nlinarith
      field_simp
      ring
  · -- class 831: alpha = 210, g = 2, beta = 208
    have hnform : n = 839 * k + 831 := by omega
    rw [hnform]
    refine ⟨210 * k + 208, 210 * (839 * k + 831), 105 * (210 * k + 208) * (839 * k + 831), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 210 * k + 208 := by nlinarith
      have hk2 : (0 : ℚ) < 839 * k + 831 := by nlinarith
      field_simp
      ring
  · -- class 827: alpha = 210, g = 3, beta = 207
    have hnform : n = 839 * k + 827 := by omega
    rw [hnform]
    refine ⟨210 * k + 207, 210 * (839 * k + 827), 70 * (210 * k + 207) * (839 * k + 827), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 210 * k + 207 := by nlinarith
      have hk2 : (0 : ℚ) < 839 * k + 827 := by nlinarith
      field_simp
      ring
  · -- class 819: alpha = 210, g = 5, beta = 205
    have hnform : n = 839 * k + 819 := by omega
    rw [hnform]
    refine ⟨210 * k + 205, 210 * (839 * k + 819), 42 * (210 * k + 205) * (839 * k + 819), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 210 * k + 205 := by nlinarith
      have hk2 : (0 : ℚ) < 839 * k + 819 := by nlinarith
      field_simp
      ring
  · -- class 815: alpha = 210, g = 6, beta = 204
    have hnform : n = 839 * k + 815 := by omega
    rw [hnform]
    refine ⟨210 * k + 204, 210 * (839 * k + 815), 35 * (210 * k + 204) * (839 * k + 815), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 210 * k + 204 := by nlinarith
      have hk2 : (0 : ℚ) < 839 * k + 815 := by nlinarith
      field_simp
      ring
  · -- class 811: alpha = 210, g = 7, beta = 203
    have hnform : n = 839 * k + 811 := by omega
    rw [hnform]
    refine ⟨210 * k + 203, 210 * (839 * k + 811), 30 * (210 * k + 203) * (839 * k + 811), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 210 * k + 203 := by nlinarith
      have hk2 : (0 : ℚ) < 839 * k + 811 := by nlinarith
      field_simp
      ring
  · -- class 799: alpha = 210, g = 10, beta = 200
    have hnform : n = 839 * k + 799 := by omega
    rw [hnform]
    refine ⟨210 * k + 200, 210 * (839 * k + 799), 21 * (210 * k + 200) * (839 * k + 799), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 210 * k + 200 := by nlinarith
      have hk2 : (0 : ℚ) < 839 * k + 799 := by nlinarith
      field_simp
      ring
  · -- class 783: alpha = 210, g = 14, beta = 196
    have hnform : n = 839 * k + 783 := by omega
    rw [hnform]
    refine ⟨210 * k + 196, 210 * (839 * k + 783), 15 * (210 * k + 196) * (839 * k + 783), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 210 * k + 196 := by nlinarith
      have hk2 : (0 : ℚ) < 839 * k + 783 := by nlinarith
      field_simp
      ring
  · -- class 779: alpha = 210, g = 15, beta = 195
    have hnform : n = 839 * k + 779 := by omega
    rw [hnform]
    refine ⟨210 * k + 195, 210 * (839 * k + 779), 14 * (210 * k + 195) * (839 * k + 779), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 210 * k + 195 := by nlinarith
      have hk2 : (0 : ℚ) < 839 * k + 779 := by nlinarith
      field_simp
      ring
  · -- class 755: alpha = 210, g = 21, beta = 189
    have hnform : n = 839 * k + 755 := by omega
    rw [hnform]
    refine ⟨210 * k + 189, 210 * (839 * k + 755), 10 * (210 * k + 189) * (839 * k + 755), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 210 * k + 189 := by nlinarith
      have hk2 : (0 : ℚ) < 839 * k + 755 := by nlinarith
      field_simp
      ring
  · -- class 719: alpha = 210, g = 30, beta = 180
    have hnform : n = 839 * k + 719 := by omega
    rw [hnform]
    refine ⟨210 * k + 180, 210 * (839 * k + 719), 7 * (210 * k + 180) * (839 * k + 719), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 210 * k + 180 := by nlinarith
      have hk2 : (0 : ℚ) < 839 * k + 719 := by nlinarith
      field_simp
      ring
  · -- class 699: alpha = 210, g = 35, beta = 175
    have hnform : n = 839 * k + 699 := by omega
    rw [hnform]
    refine ⟨210 * k + 175, 210 * (839 * k + 699), 6 * (210 * k + 175) * (839 * k + 699), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 210 * k + 175 := by nlinarith
      have hk2 : (0 : ℚ) < 839 * k + 699 := by nlinarith
      field_simp
      ring
  · -- class 671: alpha = 210, g = 42, beta = 168
    have hnform : n = 839 * k + 671 := by omega
    rw [hnform]
    refine ⟨210 * k + 168, 210 * (839 * k + 671), 5 * (210 * k + 168) * (839 * k + 671), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 210 * k + 168 := by nlinarith
      have hk2 : (0 : ℚ) < 839 * k + 671 := by nlinarith
      field_simp
      ring
  · -- class 559: alpha = 210, g = 70, beta = 140
    have hnform : n = 839 * k + 559 := by omega
    rw [hnform]
    refine ⟨210 * k + 140, 210 * (839 * k + 559), 3 * (210 * k + 140) * (839 * k + 559), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 210 * k + 140 := by nlinarith
      have hk2 : (0 : ℚ) < 839 * k + 559 := by nlinarith
      field_simp
      ring
  · -- class 419: alpha = 210, g = 105, beta = 105
    have hnform : n = 839 * k + 419 := by omega
    by_cases hk0 : k = 0
    · have h419 : n = 419 := by omega
      rw [h419]
      refine ⟨105, 43996, 1935604020, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨210 * k + 105, 210 * (839 * k + 419), 2 * (210 * k + 105) * (839 * k + 419), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 210 * k + 105 := by nlinarith
        have hk2 : (0 : ℚ) < 839 * k + 419 := by nlinarith
        field_simp
        ring
