-- Prove2me | solution 2 for ErdosStraus242.family_mod631
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:19.542478+00:00
-- url     : https://prove2.me/submissions/7e18ec36-486c-497c-b0e6-74199c60a131

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 631 ∈ ({627, 623, 315} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 631
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 631 * k + n % 631 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 627: alpha = 158, g = 1, beta = 157
    have hnform : n = 631 * k + 627 := by omega
    rw [hnform]
    refine ⟨158 * k + 157, 158 * (631 * k + 627), 158 * (158 * k + 157) * (631 * k + 627), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 158 * k + 157 := by nlinarith
      have hk2 : (0 : ℚ) < 631 * k + 627 := by nlinarith
      field_simp
      ring
  · -- class 623: alpha = 158, g = 2, beta = 156
    have hnform : n = 631 * k + 623 := by omega
    rw [hnform]
    refine ⟨158 * k + 156, 158 * (631 * k + 623), 79 * (158 * k + 156) * (631 * k + 623), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 158 * k + 156 := by nlinarith
      have hk2 : (0 : ℚ) < 631 * k + 623 := by nlinarith
      field_simp
      ring
  · -- class 315: alpha = 158, g = 79, beta = 79
    have hnform : n = 631 * k + 315 := by omega
    by_cases hk0 : k = 0
    · have h315 : n = 315 := by omega
      rw [h315]
      refine ⟨79, 24886, 619288110, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨158 * k + 79, 158 * (631 * k + 315), 2 * (158 * k + 79) * (631 * k + 315), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 158 * k + 79 := by nlinarith
        have hk2 : (0 : ℚ) < 631 * k + 315 := by nlinarith
        field_simp
        ring
