-- Prove2me | solution 1 for ErdosStraus242.family_mod611
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:01.461294+00:00
-- url     : https://prove2.me/submissions/c6d1bc01-98a0-4a66-8f7e-5d967eb8b369

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 611 ∈ ({607, 599, 575, 543, 407} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 611
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 611 * k + n % 611 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h
  · -- class 607: alpha = 153, g = 1, beta = 152
    have hnform : n = 611 * k + 607 := by omega
    rw [hnform]
    refine ⟨153 * k + 152, 153 * (611 * k + 607), 153 * (153 * k + 152) * (611 * k + 607), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 153 * k + 152 := by nlinarith
      have hk2 : (0 : ℚ) < 611 * k + 607 := by nlinarith
      field_simp
      ring
  · -- class 599: alpha = 153, g = 3, beta = 150
    have hnform : n = 611 * k + 599 := by omega
    rw [hnform]
    refine ⟨153 * k + 150, 153 * (611 * k + 599), 51 * (153 * k + 150) * (611 * k + 599), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 153 * k + 150 := by nlinarith
      have hk2 : (0 : ℚ) < 611 * k + 599 := by nlinarith
      field_simp
      ring
  · -- class 575: alpha = 153, g = 9, beta = 144
    have hnform : n = 611 * k + 575 := by omega
    rw [hnform]
    refine ⟨153 * k + 144, 153 * (611 * k + 575), 17 * (153 * k + 144) * (611 * k + 575), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 153 * k + 144 := by nlinarith
      have hk2 : (0 : ℚ) < 611 * k + 575 := by nlinarith
      field_simp
      ring
  · -- class 543: alpha = 153, g = 17, beta = 136
    have hnform : n = 611 * k + 543 := by omega
    rw [hnform]
    refine ⟨153 * k + 136, 153 * (611 * k + 543), 9 * (153 * k + 136) * (611 * k + 543), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 153 * k + 136 := by nlinarith
      have hk2 : (0 : ℚ) < 611 * k + 543 := by nlinarith
      field_simp
      ring
  · -- class 407: alpha = 153, g = 51, beta = 102
    have hnform : n = 611 * k + 407 := by omega
    rw [hnform]
    refine ⟨153 * k + 102, 153 * (611 * k + 407), 3 * (153 * k + 102) * (611 * k + 407), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 153 * k + 102 := by nlinarith
      have hk2 : (0 : ℚ) < 611 * k + 407 := by nlinarith
      field_simp
      ring
