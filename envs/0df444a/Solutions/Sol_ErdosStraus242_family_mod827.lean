-- Prove2me | solution 1 for ErdosStraus242.family_mod827
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:32.945161+00:00
-- url     : https://prove2.me/submissions/cbc13469-7af6-4eff-9b44-306f5046ba15

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 827 ∈ ({823, 815, 791, 735, 551} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 827
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 827 * k + n % 827 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h
  · -- class 823: alpha = 207, g = 1, beta = 206
    have hnform : n = 827 * k + 823 := by omega
    rw [hnform]
    refine ⟨207 * k + 206, 207 * (827 * k + 823), 207 * (207 * k + 206) * (827 * k + 823), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 207 * k + 206 := by nlinarith
      have hk2 : (0 : ℚ) < 827 * k + 823 := by nlinarith
      field_simp
      ring
  · -- class 815: alpha = 207, g = 3, beta = 204
    have hnform : n = 827 * k + 815 := by omega
    rw [hnform]
    refine ⟨207 * k + 204, 207 * (827 * k + 815), 69 * (207 * k + 204) * (827 * k + 815), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 207 * k + 204 := by nlinarith
      have hk2 : (0 : ℚ) < 827 * k + 815 := by nlinarith
      field_simp
      ring
  · -- class 791: alpha = 207, g = 9, beta = 198
    have hnform : n = 827 * k + 791 := by omega
    rw [hnform]
    refine ⟨207 * k + 198, 207 * (827 * k + 791), 23 * (207 * k + 198) * (827 * k + 791), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 207 * k + 198 := by nlinarith
      have hk2 : (0 : ℚ) < 827 * k + 791 := by nlinarith
      field_simp
      ring
  · -- class 735: alpha = 207, g = 23, beta = 184
    have hnform : n = 827 * k + 735 := by omega
    rw [hnform]
    refine ⟨207 * k + 184, 207 * (827 * k + 735), 9 * (207 * k + 184) * (827 * k + 735), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 207 * k + 184 := by nlinarith
      have hk2 : (0 : ℚ) < 827 * k + 735 := by nlinarith
      field_simp
      ring
  · -- class 551: alpha = 207, g = 69, beta = 138
    have hnform : n = 827 * k + 551 := by omega
    rw [hnform]
    refine ⟨207 * k + 138, 207 * (827 * k + 551), 3 * (207 * k + 138) * (827 * k + 551), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 207 * k + 138 := by nlinarith
      have hk2 : (0 : ℚ) < 827 * k + 551 := by nlinarith
      field_simp
      ring
