-- Prove2me | solution 1 for ErdosStraus242.family_mod823
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:32.434482+00:00
-- url     : https://prove2.me/submissions/7004eea7-c827-4ae2-9927-2f9d897b27c9

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 823 ∈ ({819, 815, 411} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 823
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 823 * k + n % 823 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 819: alpha = 206, g = 1, beta = 205
    have hnform : n = 823 * k + 819 := by omega
    rw [hnform]
    refine ⟨206 * k + 205, 206 * (823 * k + 819), 206 * (206 * k + 205) * (823 * k + 819), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 206 * k + 205 := by nlinarith
      have hk2 : (0 : ℚ) < 823 * k + 819 := by nlinarith
      field_simp
      ring
  · -- class 815: alpha = 206, g = 2, beta = 204
    have hnform : n = 823 * k + 815 := by omega
    rw [hnform]
    refine ⟨206 * k + 204, 206 * (823 * k + 815), 103 * (206 * k + 204) * (823 * k + 815), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 206 * k + 204 := by nlinarith
      have hk2 : (0 : ℚ) < 823 * k + 815 := by nlinarith
      field_simp
      ring
  · -- class 411: alpha = 206, g = 103, beta = 103
    have hnform : n = 823 * k + 411 := by omega
    by_cases hk0 : k = 0
    · have h411 : n = 411 := by omega
      rw [h411]
      refine ⟨103, 42334, 1792125222, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨206 * k + 103, 206 * (823 * k + 411), 2 * (206 * k + 103) * (823 * k + 411), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 206 * k + 103 := by nlinarith
        have hk2 : (0 : ℚ) < 823 * k + 411 := by nlinarith
        field_simp
        ring
