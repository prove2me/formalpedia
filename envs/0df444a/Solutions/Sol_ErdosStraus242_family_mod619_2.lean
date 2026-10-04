-- Prove2me | solution 2 for ErdosStraus242.family_mod619
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:19.089897+00:00
-- url     : https://prove2.me/submissions/44dc080e-bd04-471f-a672-752fc17cb47f

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 619 ∈ ({615, 599, 495} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 619
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 619 * k + n % 619 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 615: alpha = 155, g = 1, beta = 154
    have hnform : n = 619 * k + 615 := by omega
    rw [hnform]
    refine ⟨155 * k + 154, 155 * (619 * k + 615), 155 * (155 * k + 154) * (619 * k + 615), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 155 * k + 154 := by nlinarith
      have hk2 : (0 : ℚ) < 619 * k + 615 := by nlinarith
      field_simp
      ring
  · -- class 599: alpha = 155, g = 5, beta = 150
    have hnform : n = 619 * k + 599 := by omega
    rw [hnform]
    refine ⟨155 * k + 150, 155 * (619 * k + 599), 31 * (155 * k + 150) * (619 * k + 599), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 155 * k + 150 := by nlinarith
      have hk2 : (0 : ℚ) < 619 * k + 599 := by nlinarith
      field_simp
      ring
  · -- class 495: alpha = 155, g = 31, beta = 124
    have hnform : n = 619 * k + 495 := by omega
    rw [hnform]
    refine ⟨155 * k + 124, 155 * (619 * k + 495), 5 * (155 * k + 124) * (619 * k + 495), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 155 * k + 124 := by nlinarith
      have hk2 : (0 : ℚ) < 619 * k + 495 := by nlinarith
      field_simp
      ring
