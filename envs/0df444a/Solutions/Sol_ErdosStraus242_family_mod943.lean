-- Prove2me | solution 1 for ErdosStraus242.family_mod943
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:13:04.594907+00:00
-- url     : https://prove2.me/submissions/faf63443-b15b-4910-9e6e-9fde27a8456a

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 943 ∈ ({939, 935, 927, 707, 471} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 943
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 943 * k + n % 943 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h
  · -- class 939: alpha = 236, g = 1, beta = 235
    have hnform : n = 943 * k + 939 := by omega
    rw [hnform]
    refine ⟨236 * k + 235, 236 * (943 * k + 939), 236 * (236 * k + 235) * (943 * k + 939), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 236 * k + 235 := by nlinarith
      have hk2 : (0 : ℚ) < 943 * k + 939 := by nlinarith
      field_simp
      ring
  · -- class 935: alpha = 236, g = 2, beta = 234
    have hnform : n = 943 * k + 935 := by omega
    rw [hnform]
    refine ⟨236 * k + 234, 236 * (943 * k + 935), 118 * (236 * k + 234) * (943 * k + 935), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 236 * k + 234 := by nlinarith
      have hk2 : (0 : ℚ) < 943 * k + 935 := by nlinarith
      field_simp
      ring
  · -- class 927: alpha = 236, g = 4, beta = 232
    have hnform : n = 943 * k + 927 := by omega
    rw [hnform]
    refine ⟨236 * k + 232, 236 * (943 * k + 927), 59 * (236 * k + 232) * (943 * k + 927), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 236 * k + 232 := by nlinarith
      have hk2 : (0 : ℚ) < 943 * k + 927 := by nlinarith
      field_simp
      ring
  · -- class 707: alpha = 236, g = 59, beta = 177
    have hnform : n = 943 * k + 707 := by omega
    rw [hnform]
    refine ⟨236 * k + 177, 236 * (943 * k + 707), 4 * (236 * k + 177) * (943 * k + 707), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 236 * k + 177 := by nlinarith
      have hk2 : (0 : ℚ) < 943 * k + 707 := by nlinarith
      field_simp
      ring
  · -- class 471: alpha = 236, g = 118, beta = 118
    have hnform : n = 943 * k + 471 := by omega
    by_cases hk0 : k = 0
    · have h471 : n = 471 := by omega
      rw [h471]
      refine ⟨118, 55579, 3088969662, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨236 * k + 118, 236 * (943 * k + 471), 2 * (236 * k + 118) * (943 * k + 471), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 236 * k + 118 := by nlinarith
        have hk2 : (0 : ℚ) < 943 * k + 471 := by nlinarith
        field_simp
        ring
