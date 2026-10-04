-- Prove2me | solution 1 for ErdosStraus242.family_mod739
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:26.99299+00:00
-- url     : https://prove2.me/submissions/16d85d44-ccb7-4cb4-b0b6-120d992ea909

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 739 ∈ ({735, 719, 591} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 739
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 739 * k + n % 739 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 735: alpha = 185, g = 1, beta = 184
    have hnform : n = 739 * k + 735 := by omega
    rw [hnform]
    refine ⟨185 * k + 184, 185 * (739 * k + 735), 185 * (185 * k + 184) * (739 * k + 735), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 185 * k + 184 := by nlinarith
      have hk2 : (0 : ℚ) < 739 * k + 735 := by nlinarith
      field_simp
      ring
  · -- class 719: alpha = 185, g = 5, beta = 180
    have hnform : n = 739 * k + 719 := by omega
    rw [hnform]
    refine ⟨185 * k + 180, 185 * (739 * k + 719), 37 * (185 * k + 180) * (739 * k + 719), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 185 * k + 180 := by nlinarith
      have hk2 : (0 : ℚ) < 739 * k + 719 := by nlinarith
      field_simp
      ring
  · -- class 591: alpha = 185, g = 37, beta = 148
    have hnform : n = 739 * k + 591 := by omega
    rw [hnform]
    refine ⟨185 * k + 148, 185 * (739 * k + 591), 5 * (185 * k + 148) * (739 * k + 591), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 185 * k + 148 := by nlinarith
      have hk2 : (0 : ℚ) < 739 * k + 591 := by nlinarith
      field_simp
      ring
