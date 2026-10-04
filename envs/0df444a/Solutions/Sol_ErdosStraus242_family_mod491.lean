-- Prove2me | solution 1 for ErdosStraus242.family_mod491
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:34.573315+00:00
-- url     : https://prove2.me/submissions/3ad6959d-6387-439c-8d1a-0e8630dd42e6

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 491 ∈ ({487, 479, 327} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 491
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 491 * k + n % 491 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 487: alpha = 123, g = 1, beta = 122
    have hnform : n = 491 * k + 487 := by omega
    rw [hnform]
    refine ⟨123 * k + 122, 123 * (491 * k + 487), 123 * (123 * k + 122) * (491 * k + 487), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 123 * k + 122 := by nlinarith
      have hk2 : (0 : ℚ) < 491 * k + 487 := by nlinarith
      field_simp
      ring
  · -- class 479: alpha = 123, g = 3, beta = 120
    have hnform : n = 491 * k + 479 := by omega
    rw [hnform]
    refine ⟨123 * k + 120, 123 * (491 * k + 479), 41 * (123 * k + 120) * (491 * k + 479), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 123 * k + 120 := by nlinarith
      have hk2 : (0 : ℚ) < 491 * k + 479 := by nlinarith
      field_simp
      ring
  · -- class 327: alpha = 123, g = 41, beta = 82
    have hnform : n = 491 * k + 327 := by omega
    rw [hnform]
    refine ⟨123 * k + 82, 123 * (491 * k + 327), 3 * (123 * k + 82) * (491 * k + 327), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 123 * k + 82 := by nlinarith
      have hk2 : (0 : ℚ) < 491 * k + 327 := by nlinarith
      field_simp
      ring
