-- Prove2me | solution 1 for ErdosStraus242.family_mod871
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:12:59.328434+00:00
-- url     : https://prove2.me/submissions/dff3f357-a198-4c0c-bd01-5d4745152ef6

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 871 ∈ ({867, 863, 435} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 871
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 871 * k + n % 871 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 867: alpha = 218, g = 1, beta = 217
    have hnform : n = 871 * k + 867 := by omega
    rw [hnform]
    refine ⟨218 * k + 217, 218 * (871 * k + 867), 218 * (218 * k + 217) * (871 * k + 867), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 218 * k + 217 := by nlinarith
      have hk2 : (0 : ℚ) < 871 * k + 867 := by nlinarith
      field_simp
      ring
  · -- class 863: alpha = 218, g = 2, beta = 216
    have hnform : n = 871 * k + 863 := by omega
    rw [hnform]
    refine ⟨218 * k + 216, 218 * (871 * k + 863), 109 * (218 * k + 216) * (871 * k + 863), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 218 * k + 216 := by nlinarith
      have hk2 : (0 : ℚ) < 871 * k + 863 := by nlinarith
      field_simp
      ring
  · -- class 435: alpha = 218, g = 109, beta = 109
    have hnform : n = 871 * k + 435 := by omega
    by_cases hk0 : k = 0
    · have h435 : n = 435 := by omega
      rw [h435]
      refine ⟨109, 47416, 2248229640, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨218 * k + 109, 218 * (871 * k + 435), 2 * (218 * k + 109) * (871 * k + 435), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 218 * k + 109 := by nlinarith
        have hk2 : (0 : ℚ) < 871 * k + 435 := by nlinarith
        field_simp
        ring
