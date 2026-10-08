-- Prove2me | solution 1 for ErdosStraus242.family_mod911
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:13:02.650495+00:00
-- url     : https://prove2.me/submissions/afeccd47-0b81-404d-9579-b3958f28a1f5

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 911 ∈ ({907, 903, 899, 895, 887, 863, 835, 759, 683, 607, 455} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 911
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 911 * k + n % 911 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h
  · -- class 907: alpha = 228, g = 1, beta = 227
    have hnform : n = 911 * k + 907 := by omega
    rw [hnform]
    refine ⟨228 * k + 227, 228 * (911 * k + 907), 228 * (228 * k + 227) * (911 * k + 907), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 228 * k + 227 := by nlinarith
      have hk2 : (0 : ℚ) < 911 * k + 907 := by nlinarith
      field_simp
      ring
  · -- class 903: alpha = 228, g = 2, beta = 226
    have hnform : n = 911 * k + 903 := by omega
    rw [hnform]
    refine ⟨228 * k + 226, 228 * (911 * k + 903), 114 * (228 * k + 226) * (911 * k + 903), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 228 * k + 226 := by nlinarith
      have hk2 : (0 : ℚ) < 911 * k + 903 := by nlinarith
      field_simp
      ring
  · -- class 899: alpha = 228, g = 3, beta = 225
    have hnform : n = 911 * k + 899 := by omega
    rw [hnform]
    refine ⟨228 * k + 225, 228 * (911 * k + 899), 76 * (228 * k + 225) * (911 * k + 899), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 228 * k + 225 := by nlinarith
      have hk2 : (0 : ℚ) < 911 * k + 899 := by nlinarith
      field_simp
      ring
  · -- class 895: alpha = 228, g = 4, beta = 224
    have hnform : n = 911 * k + 895 := by omega
    rw [hnform]
    refine ⟨228 * k + 224, 228 * (911 * k + 895), 57 * (228 * k + 224) * (911 * k + 895), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 228 * k + 224 := by nlinarith
      have hk2 : (0 : ℚ) < 911 * k + 895 := by nlinarith
      field_simp
      ring
  · -- class 887: alpha = 228, g = 6, beta = 222
    have hnform : n = 911 * k + 887 := by omega
    rw [hnform]
    refine ⟨228 * k + 222, 228 * (911 * k + 887), 38 * (228 * k + 222) * (911 * k + 887), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 228 * k + 222 := by nlinarith
      have hk2 : (0 : ℚ) < 911 * k + 887 := by nlinarith
      field_simp
      ring
  · -- class 863: alpha = 228, g = 12, beta = 216
    have hnform : n = 911 * k + 863 := by omega
    rw [hnform]
    refine ⟨228 * k + 216, 228 * (911 * k + 863), 19 * (228 * k + 216) * (911 * k + 863), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 228 * k + 216 := by nlinarith
      have hk2 : (0 : ℚ) < 911 * k + 863 := by nlinarith
      field_simp
      ring
  · -- class 835: alpha = 228, g = 19, beta = 209
    have hnform : n = 911 * k + 835 := by omega
    rw [hnform]
    refine ⟨228 * k + 209, 228 * (911 * k + 835), 12 * (228 * k + 209) * (911 * k + 835), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 228 * k + 209 := by nlinarith
      have hk2 : (0 : ℚ) < 911 * k + 835 := by nlinarith
      field_simp
      ring
  · -- class 759: alpha = 228, g = 38, beta = 190
    have hnform : n = 911 * k + 759 := by omega
    rw [hnform]
    refine ⟨228 * k + 190, 228 * (911 * k + 759), 6 * (228 * k + 190) * (911 * k + 759), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 228 * k + 190 := by nlinarith
      have hk2 : (0 : ℚ) < 911 * k + 759 := by nlinarith
      field_simp
      ring
  · -- class 683: alpha = 228, g = 57, beta = 171
    have hnform : n = 911 * k + 683 := by omega
    rw [hnform]
    refine ⟨228 * k + 171, 228 * (911 * k + 683), 4 * (228 * k + 171) * (911 * k + 683), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 228 * k + 171 := by nlinarith
      have hk2 : (0 : ℚ) < 911 * k + 683 := by nlinarith
      field_simp
      ring
  · -- class 607: alpha = 228, g = 76, beta = 152
    have hnform : n = 911 * k + 607 := by omega
    rw [hnform]
    refine ⟨228 * k + 152, 228 * (911 * k + 607), 3 * (228 * k + 152) * (911 * k + 607), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 228 * k + 152 := by nlinarith
      have hk2 : (0 : ℚ) < 911 * k + 607 := by nlinarith
      field_simp
      ring
  · -- class 455: alpha = 228, g = 114, beta = 114
    have hnform : n = 911 * k + 455 := by omega
    by_cases hk0 : k = 0
    · have h455 : n = 455 := by omega
      rw [h455]
      refine ⟨114, 51871, 2690548770, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨228 * k + 114, 228 * (911 * k + 455), 2 * (228 * k + 114) * (911 * k + 455), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 228 * k + 114 := by nlinarith
        have hk2 : (0 : ℚ) < 911 * k + 455 := by nlinarith
        field_simp
        ring
