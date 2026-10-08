-- Prove2me | solution 1 for ErdosStraus242.family_mod1111
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:40.416728+00:00
-- url     : https://prove2.me/submissions/738c7169-87a4-4242-90a5-4f06b7f32a3b

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1111 ∈ ({1107, 1103, 555} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1111
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1111 * k + n % 1111 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 1107: alpha = 278, g = 1, beta = 277
    have hnform : n = 1111 * k + 1107 := by omega
    rw [hnform]
    refine ⟨278 * k + 277, 278 * (1111 * k + 1107), 278 * (278 * k + 277) * (1111 * k + 1107), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 278 * k + 277 := by nlinarith
      have hk2 : (0 : ℚ) < 1111 * k + 1107 := by nlinarith
      field_simp
      ring
  · -- class 1103: alpha = 278, g = 2, beta = 276
    have hnform : n = 1111 * k + 1103 := by omega
    rw [hnform]
    refine ⟨278 * k + 276, 278 * (1111 * k + 1103), 139 * (278 * k + 276) * (1111 * k + 1103), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 278 * k + 276 := by nlinarith
      have hk2 : (0 : ℚ) < 1111 * k + 1103 := by nlinarith
      field_simp
      ring
  · -- class 555: alpha = 278, g = 139, beta = 139
    have hnform : n = 1111 * k + 555 := by omega
    by_cases hk0 : k = 0
    · have h555 : n = 555 := by omega
      rw [h555]
      refine ⟨139, 77146, 5951428170, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨278 * k + 139, 278 * (1111 * k + 555), 2 * (278 * k + 139) * (1111 * k + 555), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 278 * k + 139 := by nlinarith
        have hk2 : (0 : ℚ) < 1111 * k + 555 := by nlinarith
        field_simp
        ring
