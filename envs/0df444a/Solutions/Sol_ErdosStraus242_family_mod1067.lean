-- Prove2me | solution 1 for ErdosStraus242.family_mod1067
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:37.915713+00:00
-- url     : https://prove2.me/submissions/8046bc9e-6720-40ed-9eaa-347de6c0bc0b

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1067 ∈ ({1063, 1055, 711} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1067
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1067 * k + n % 1067 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 1063: alpha = 267, g = 1, beta = 266
    have hnform : n = 1067 * k + 1063 := by omega
    rw [hnform]
    refine ⟨267 * k + 266, 267 * (1067 * k + 1063), 267 * (267 * k + 266) * (1067 * k + 1063), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 267 * k + 266 := by nlinarith
      have hk2 : (0 : ℚ) < 1067 * k + 1063 := by nlinarith
      field_simp
      ring
  · -- class 1055: alpha = 267, g = 3, beta = 264
    have hnform : n = 1067 * k + 1055 := by omega
    rw [hnform]
    refine ⟨267 * k + 264, 267 * (1067 * k + 1055), 89 * (267 * k + 264) * (1067 * k + 1055), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 267 * k + 264 := by nlinarith
      have hk2 : (0 : ℚ) < 1067 * k + 1055 := by nlinarith
      field_simp
      ring
  · -- class 711: alpha = 267, g = 89, beta = 178
    have hnform : n = 1067 * k + 711 := by omega
    rw [hnform]
    refine ⟨267 * k + 178, 267 * (1067 * k + 711), 3 * (267 * k + 178) * (1067 * k + 711), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 267 * k + 178 := by nlinarith
      have hk2 : (0 : ℚ) < 1067 * k + 711 := by nlinarith
      field_simp
      ring
