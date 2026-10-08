-- Prove2me | solution 1 for ErdosStraus242.family_mod887
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:13:00.864779+00:00
-- url     : https://prove2.me/submissions/25bba082-6c25-4739-b322-be611d98cca8

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 887 ∈ ({883, 879, 875, 863, 739, 591, 443} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 887
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 887 * k + n % 887 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 883: alpha = 222, g = 1, beta = 221
    have hnform : n = 887 * k + 883 := by omega
    rw [hnform]
    refine ⟨222 * k + 221, 222 * (887 * k + 883), 222 * (222 * k + 221) * (887 * k + 883), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 222 * k + 221 := by nlinarith
      have hk2 : (0 : ℚ) < 887 * k + 883 := by nlinarith
      field_simp
      ring
  · -- class 879: alpha = 222, g = 2, beta = 220
    have hnform : n = 887 * k + 879 := by omega
    rw [hnform]
    refine ⟨222 * k + 220, 222 * (887 * k + 879), 111 * (222 * k + 220) * (887 * k + 879), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 222 * k + 220 := by nlinarith
      have hk2 : (0 : ℚ) < 887 * k + 879 := by nlinarith
      field_simp
      ring
  · -- class 875: alpha = 222, g = 3, beta = 219
    have hnform : n = 887 * k + 875 := by omega
    rw [hnform]
    refine ⟨222 * k + 219, 222 * (887 * k + 875), 74 * (222 * k + 219) * (887 * k + 875), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 222 * k + 219 := by nlinarith
      have hk2 : (0 : ℚ) < 887 * k + 875 := by nlinarith
      field_simp
      ring
  · -- class 863: alpha = 222, g = 6, beta = 216
    have hnform : n = 887 * k + 863 := by omega
    rw [hnform]
    refine ⟨222 * k + 216, 222 * (887 * k + 863), 37 * (222 * k + 216) * (887 * k + 863), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 222 * k + 216 := by nlinarith
      have hk2 : (0 : ℚ) < 887 * k + 863 := by nlinarith
      field_simp
      ring
  · -- class 739: alpha = 222, g = 37, beta = 185
    have hnform : n = 887 * k + 739 := by omega
    rw [hnform]
    refine ⟨222 * k + 185, 222 * (887 * k + 739), 6 * (222 * k + 185) * (887 * k + 739), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 222 * k + 185 := by nlinarith
      have hk2 : (0 : ℚ) < 887 * k + 739 := by nlinarith
      field_simp
      ring
  · -- class 591: alpha = 222, g = 74, beta = 148
    have hnform : n = 887 * k + 591 := by omega
    rw [hnform]
    refine ⟨222 * k + 148, 222 * (887 * k + 591), 3 * (222 * k + 148) * (887 * k + 591), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 222 * k + 148 := by nlinarith
      have hk2 : (0 : ℚ) < 887 * k + 591 := by nlinarith
      field_simp
      ring
  · -- class 443: alpha = 222, g = 111, beta = 111
    have hnform : n = 887 * k + 443 := by omega
    by_cases hk0 : k = 0
    · have h443 : n = 443 := by omega
      rw [h443]
      refine ⟨111, 49174, 2418033102, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨222 * k + 111, 222 * (887 * k + 443), 2 * (222 * k + 111) * (887 * k + 443), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 222 * k + 111 := by nlinarith
        have hk2 : (0 : ℚ) < 887 * k + 443 := by nlinarith
        field_simp
        ring
