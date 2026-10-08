-- Prove2me | solution 1 for ErdosStraus242.family_mod1147
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:41.853227+00:00
-- url     : https://prove2.me/submissions/094c3ac3-7de0-41dd-b19e-cedef0ff644d

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1147 ∈ ({1143, 1119, 983} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1147
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1147 * k + n % 1147 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 1143: alpha = 287, g = 1, beta = 286
    have hnform : n = 1147 * k + 1143 := by omega
    rw [hnform]
    refine ⟨287 * k + 286, 287 * (1147 * k + 1143), 287 * (287 * k + 286) * (1147 * k + 1143), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 287 * k + 286 := by nlinarith
      have hk2 : (0 : ℚ) < 1147 * k + 1143 := by nlinarith
      field_simp
      ring
  · -- class 1119: alpha = 287, g = 7, beta = 280
    have hnform : n = 1147 * k + 1119 := by omega
    rw [hnform]
    refine ⟨287 * k + 280, 287 * (1147 * k + 1119), 41 * (287 * k + 280) * (1147 * k + 1119), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 287 * k + 280 := by nlinarith
      have hk2 : (0 : ℚ) < 1147 * k + 1119 := by nlinarith
      field_simp
      ring
  · -- class 983: alpha = 287, g = 41, beta = 246
    have hnform : n = 1147 * k + 983 := by omega
    rw [hnform]
    refine ⟨287 * k + 246, 287 * (1147 * k + 983), 7 * (287 * k + 246) * (1147 * k + 983), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 287 * k + 246 := by nlinarith
      have hk2 : (0 : ℚ) < 1147 * k + 983 := by nlinarith
      field_simp
      ring
