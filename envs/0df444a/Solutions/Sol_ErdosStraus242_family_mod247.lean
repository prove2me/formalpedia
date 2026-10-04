-- Prove2me | solution 1 for ErdosStraus242.family_mod247
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:31.620733+00:00
-- url     : https://prove2.me/submissions/aee013ba-e70b-4977-a63f-ee324bc8ec80

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 247 ∈ ({243, 239, 123} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 247
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 247 * k + n % 247 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 243: alpha = 62, g = 1, beta = 61
    have hnform : n = 247 * k + 243 := by omega
    rw [hnform]
    refine ⟨62 * k + 61, 62 * (247 * k + 243), 62 * (62 * k + 61) * (247 * k + 243), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 62 * k + 61 := by nlinarith
      have hk2 : (0 : ℚ) < 247 * k + 243 := by nlinarith
      field_simp
      ring
  · -- class 239: alpha = 62, g = 2, beta = 60
    have hnform : n = 247 * k + 239 := by omega
    rw [hnform]
    refine ⟨62 * k + 60, 62 * (247 * k + 239), 31 * (62 * k + 60) * (247 * k + 239), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 62 * k + 60 := by nlinarith
      have hk2 : (0 : ℚ) < 247 * k + 239 := by nlinarith
      field_simp
      ring
  · -- class 123: alpha = 62, g = 31, beta = 31
    have hnform : n = 247 * k + 123 := by omega
    by_cases hk0 : k = 0
    · have h123 : n = 123 := by omega
      rw [h123]
      refine ⟨31, 3814, 14542782, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨62 * k + 31, 62 * (247 * k + 123), 2 * (62 * k + 31) * (247 * k + 123), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 62 * k + 31 := by nlinarith
        have hk2 : (0 : ℚ) < 247 * k + 123 := by nlinarith
        field_simp
        ring
