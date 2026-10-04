-- Prove2me | solution 1 for ErdosStraus242.family_mod391
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:32.09539+00:00
-- url     : https://prove2.me/submissions/8eb78a20-8405-4fed-85f9-1d6c1deb370d

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 391 ∈ ({387, 383, 363, 335, 195} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 391
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 391 * k + n % 391 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h
  · -- class 387: alpha = 98, g = 1, beta = 97
    have hnform : n = 391 * k + 387 := by omega
    rw [hnform]
    refine ⟨98 * k + 97, 98 * (391 * k + 387), 98 * (98 * k + 97) * (391 * k + 387), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 98 * k + 97 := by nlinarith
      have hk2 : (0 : ℚ) < 391 * k + 387 := by nlinarith
      field_simp
      ring
  · -- class 383: alpha = 98, g = 2, beta = 96
    have hnform : n = 391 * k + 383 := by omega
    rw [hnform]
    refine ⟨98 * k + 96, 98 * (391 * k + 383), 49 * (98 * k + 96) * (391 * k + 383), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 98 * k + 96 := by nlinarith
      have hk2 : (0 : ℚ) < 391 * k + 383 := by nlinarith
      field_simp
      ring
  · -- class 363: alpha = 98, g = 7, beta = 91
    have hnform : n = 391 * k + 363 := by omega
    rw [hnform]
    refine ⟨98 * k + 91, 98 * (391 * k + 363), 14 * (98 * k + 91) * (391 * k + 363), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 98 * k + 91 := by nlinarith
      have hk2 : (0 : ℚ) < 391 * k + 363 := by nlinarith
      field_simp
      ring
  · -- class 335: alpha = 98, g = 14, beta = 84
    have hnform : n = 391 * k + 335 := by omega
    rw [hnform]
    refine ⟨98 * k + 84, 98 * (391 * k + 335), 7 * (98 * k + 84) * (391 * k + 335), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 98 * k + 84 := by nlinarith
      have hk2 : (0 : ℚ) < 391 * k + 335 := by nlinarith
      field_simp
      ring
  · -- class 195: alpha = 98, g = 49, beta = 49
    have hnform : n = 391 * k + 195 := by omega
    by_cases hk0 : k = 0
    · have h195 : n = 195 := by omega
      rw [h195]
      refine ⟨49, 9556, 91307580, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨98 * k + 49, 98 * (391 * k + 195), 2 * (98 * k + 49) * (391 * k + 195), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 98 * k + 49 := by nlinarith
        have hk2 : (0 : ℚ) < 391 * k + 195 := by nlinarith
        field_simp
        ring
