-- Prove2me | solution 1 for ErdosStraus242.family_mod859
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:12:58.086006+00:00
-- url     : https://prove2.me/submissions/a67b775b-559f-449d-945c-a010b935183f

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 859 ∈ ({855, 839, 687} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 859
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 859 * k + n % 859 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 855: alpha = 215, g = 1, beta = 214
    have hnform : n = 859 * k + 855 := by omega
    rw [hnform]
    refine ⟨215 * k + 214, 215 * (859 * k + 855), 215 * (215 * k + 214) * (859 * k + 855), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 215 * k + 214 := by nlinarith
      have hk2 : (0 : ℚ) < 859 * k + 855 := by nlinarith
      field_simp
      ring
  · -- class 839: alpha = 215, g = 5, beta = 210
    have hnform : n = 859 * k + 839 := by omega
    rw [hnform]
    refine ⟨215 * k + 210, 215 * (859 * k + 839), 43 * (215 * k + 210) * (859 * k + 839), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 215 * k + 210 := by nlinarith
      have hk2 : (0 : ℚ) < 859 * k + 839 := by nlinarith
      field_simp
      ring
  · -- class 687: alpha = 215, g = 43, beta = 172
    have hnform : n = 859 * k + 687 := by omega
    rw [hnform]
    refine ⟨215 * k + 172, 215 * (859 * k + 687), 5 * (215 * k + 172) * (859 * k + 687), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 215 * k + 172 := by nlinarith
      have hk2 : (0 : ℚ) < 859 * k + 687 := by nlinarith
      field_simp
      ring
