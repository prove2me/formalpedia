-- Prove2me | solution 1 for ErdosStraus242.family_mod883
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:12:59.986598+00:00
-- url     : https://prove2.me/submissions/d5d6f612-4c5c-43be-bd01-1a9033ab36cf

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 883 ∈ ({879, 831, 815} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 883
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 883 * k + n % 883 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 879: alpha = 221, g = 1, beta = 220
    have hnform : n = 883 * k + 879 := by omega
    rw [hnform]
    refine ⟨221 * k + 220, 221 * (883 * k + 879), 221 * (221 * k + 220) * (883 * k + 879), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 221 * k + 220 := by nlinarith
      have hk2 : (0 : ℚ) < 883 * k + 879 := by nlinarith
      field_simp
      ring
  · -- class 831: alpha = 221, g = 13, beta = 208
    have hnform : n = 883 * k + 831 := by omega
    rw [hnform]
    refine ⟨221 * k + 208, 221 * (883 * k + 831), 17 * (221 * k + 208) * (883 * k + 831), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 221 * k + 208 := by nlinarith
      have hk2 : (0 : ℚ) < 883 * k + 831 := by nlinarith
      field_simp
      ring
  · -- class 815: alpha = 221, g = 17, beta = 204
    have hnform : n = 883 * k + 815 := by omega
    rw [hnform]
    refine ⟨221 * k + 204, 221 * (883 * k + 815), 13 * (221 * k + 204) * (883 * k + 815), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 221 * k + 204 := by nlinarith
      have hk2 : (0 : ℚ) < 883 * k + 815 := by nlinarith
      field_simp
      ring
