-- Prove2me | solution 1 for ErdosStraus242.family_mod811
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:31.872106+00:00
-- url     : https://prove2.me/submissions/f76ebcdd-c076-453a-9b1c-315c01879141

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 811 ∈ ({807, 783, 695} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 811
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 811 * k + n % 811 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 807: alpha = 203, g = 1, beta = 202
    have hnform : n = 811 * k + 807 := by omega
    rw [hnform]
    refine ⟨203 * k + 202, 203 * (811 * k + 807), 203 * (203 * k + 202) * (811 * k + 807), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 203 * k + 202 := by nlinarith
      have hk2 : (0 : ℚ) < 811 * k + 807 := by nlinarith
      field_simp
      ring
  · -- class 783: alpha = 203, g = 7, beta = 196
    have hnform : n = 811 * k + 783 := by omega
    rw [hnform]
    refine ⟨203 * k + 196, 203 * (811 * k + 783), 29 * (203 * k + 196) * (811 * k + 783), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 203 * k + 196 := by nlinarith
      have hk2 : (0 : ℚ) < 811 * k + 783 := by nlinarith
      field_simp
      ring
  · -- class 695: alpha = 203, g = 29, beta = 174
    have hnform : n = 811 * k + 695 := by omega
    rw [hnform]
    refine ⟨203 * k + 174, 203 * (811 * k + 695), 7 * (203 * k + 174) * (811 * k + 695), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 203 * k + 174 := by nlinarith
      have hk2 : (0 : ℚ) < 811 * k + 695 := by nlinarith
      field_simp
      ring
