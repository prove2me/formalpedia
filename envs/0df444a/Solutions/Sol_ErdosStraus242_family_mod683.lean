-- Prove2me | solution 1 for ErdosStraus242.family_mod683
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:05.62921+00:00
-- url     : https://prove2.me/submissions/469f2094-3eb4-4376-a3d5-0bdd94fc7789

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 683 ∈ ({679, 671, 647, 607, 455} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 683
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 683 * k + n % 683 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h
  · -- class 679: alpha = 171, g = 1, beta = 170
    have hnform : n = 683 * k + 679 := by omega
    rw [hnform]
    refine ⟨171 * k + 170, 171 * (683 * k + 679), 171 * (171 * k + 170) * (683 * k + 679), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 171 * k + 170 := by nlinarith
      have hk2 : (0 : ℚ) < 683 * k + 679 := by nlinarith
      field_simp
      ring
  · -- class 671: alpha = 171, g = 3, beta = 168
    have hnform : n = 683 * k + 671 := by omega
    rw [hnform]
    refine ⟨171 * k + 168, 171 * (683 * k + 671), 57 * (171 * k + 168) * (683 * k + 671), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 171 * k + 168 := by nlinarith
      have hk2 : (0 : ℚ) < 683 * k + 671 := by nlinarith
      field_simp
      ring
  · -- class 647: alpha = 171, g = 9, beta = 162
    have hnform : n = 683 * k + 647 := by omega
    rw [hnform]
    refine ⟨171 * k + 162, 171 * (683 * k + 647), 19 * (171 * k + 162) * (683 * k + 647), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 171 * k + 162 := by nlinarith
      have hk2 : (0 : ℚ) < 683 * k + 647 := by nlinarith
      field_simp
      ring
  · -- class 607: alpha = 171, g = 19, beta = 152
    have hnform : n = 683 * k + 607 := by omega
    rw [hnform]
    refine ⟨171 * k + 152, 171 * (683 * k + 607), 9 * (171 * k + 152) * (683 * k + 607), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 171 * k + 152 := by nlinarith
      have hk2 : (0 : ℚ) < 683 * k + 607 := by nlinarith
      field_simp
      ring
  · -- class 455: alpha = 171, g = 57, beta = 114
    have hnform : n = 683 * k + 455 := by omega
    rw [hnform]
    refine ⟨171 * k + 114, 171 * (683 * k + 455), 3 * (171 * k + 114) * (683 * k + 455), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 171 * k + 114 := by nlinarith
      have hk2 : (0 : ℚ) < 683 * k + 455 := by nlinarith
      field_simp
      ring
