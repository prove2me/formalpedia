-- Prove2me | solution 1 for ErdosStraus242.family_mod803
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:31.033883+00:00
-- url     : https://prove2.me/submissions/028bf309-445e-4ae1-b9c5-e5e0411e6666

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 803 ∈ ({799, 791, 535} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 803
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 803 * k + n % 803 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 799: alpha = 201, g = 1, beta = 200
    have hnform : n = 803 * k + 799 := by omega
    rw [hnform]
    refine ⟨201 * k + 200, 201 * (803 * k + 799), 201 * (201 * k + 200) * (803 * k + 799), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 201 * k + 200 := by nlinarith
      have hk2 : (0 : ℚ) < 803 * k + 799 := by nlinarith
      field_simp
      ring
  · -- class 791: alpha = 201, g = 3, beta = 198
    have hnform : n = 803 * k + 791 := by omega
    rw [hnform]
    refine ⟨201 * k + 198, 201 * (803 * k + 791), 67 * (201 * k + 198) * (803 * k + 791), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 201 * k + 198 := by nlinarith
      have hk2 : (0 : ℚ) < 803 * k + 791 := by nlinarith
      field_simp
      ring
  · -- class 535: alpha = 201, g = 67, beta = 134
    have hnform : n = 803 * k + 535 := by omega
    rw [hnform]
    refine ⟨201 * k + 134, 201 * (803 * k + 535), 3 * (201 * k + 134) * (803 * k + 535), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 201 * k + 134 := by nlinarith
      have hk2 : (0 : ℚ) < 803 * k + 535 := by nlinarith
      field_simp
      ring
