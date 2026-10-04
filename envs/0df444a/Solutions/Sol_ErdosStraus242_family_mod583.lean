-- Prove2me | solution 1 for ErdosStraus242.family_mod583
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:39.712157+00:00
-- url     : https://prove2.me/submissions/1c3f730e-d808-44f9-819f-40ce7db38107

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 583 ∈ ({579, 575, 291} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 583
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 583 * k + n % 583 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 579: alpha = 146, g = 1, beta = 145
    have hnform : n = 583 * k + 579 := by omega
    rw [hnform]
    refine ⟨146 * k + 145, 146 * (583 * k + 579), 146 * (146 * k + 145) * (583 * k + 579), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 146 * k + 145 := by nlinarith
      have hk2 : (0 : ℚ) < 583 * k + 579 := by nlinarith
      field_simp
      ring
  · -- class 575: alpha = 146, g = 2, beta = 144
    have hnform : n = 583 * k + 575 := by omega
    rw [hnform]
    refine ⟨146 * k + 144, 146 * (583 * k + 575), 73 * (146 * k + 144) * (583 * k + 575), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 146 * k + 144 := by nlinarith
      have hk2 : (0 : ℚ) < 583 * k + 575 := by nlinarith
      field_simp
      ring
  · -- class 291: alpha = 146, g = 73, beta = 73
    have hnform : n = 583 * k + 291 := by omega
    by_cases hk0 : k = 0
    · have h291 : n = 291 := by omega
      rw [h291]
      refine ⟨73, 21244, 451286292, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨146 * k + 73, 146 * (583 * k + 291), 2 * (146 * k + 73) * (583 * k + 291), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 146 * k + 73 := by nlinarith
        have hk2 : (0 : ℚ) < 583 * k + 291 := by nlinarith
        field_simp
        ring
