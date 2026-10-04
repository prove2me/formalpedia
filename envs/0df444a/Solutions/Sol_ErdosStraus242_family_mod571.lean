-- Prove2me | solution 1 for ErdosStraus242.family_mod571
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:38.859547+00:00
-- url     : https://prove2.me/submissions/2d38aed7-0ac5-431a-ac95-687ea2e54cb0

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 571 ∈ ({567, 527, 519} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 571
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 571 * k + n % 571 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 567: alpha = 143, g = 1, beta = 142
    have hnform : n = 571 * k + 567 := by omega
    rw [hnform]
    refine ⟨143 * k + 142, 143 * (571 * k + 567), 143 * (143 * k + 142) * (571 * k + 567), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 143 * k + 142 := by nlinarith
      have hk2 : (0 : ℚ) < 571 * k + 567 := by nlinarith
      field_simp
      ring
  · -- class 527: alpha = 143, g = 11, beta = 132
    have hnform : n = 571 * k + 527 := by omega
    rw [hnform]
    refine ⟨143 * k + 132, 143 * (571 * k + 527), 13 * (143 * k + 132) * (571 * k + 527), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 143 * k + 132 := by nlinarith
      have hk2 : (0 : ℚ) < 571 * k + 527 := by nlinarith
      field_simp
      ring
  · -- class 519: alpha = 143, g = 13, beta = 130
    have hnform : n = 571 * k + 519 := by omega
    rw [hnform]
    refine ⟨143 * k + 130, 143 * (571 * k + 519), 11 * (143 * k + 130) * (571 * k + 519), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 143 * k + 130 := by nlinarith
      have hk2 : (0 : ℚ) < 571 * k + 519 := by nlinarith
      field_simp
      ring
