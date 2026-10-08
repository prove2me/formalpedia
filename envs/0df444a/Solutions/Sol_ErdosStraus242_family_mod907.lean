-- Prove2me | solution 1 for ErdosStraus242.family_mod907
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:13:02.00689+00:00
-- url     : https://prove2.me/submissions/8a218684-3e07-42bb-906e-4aa7682c092f

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 907 ∈ ({903} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 907
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 907 * k + n % 907 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h
  · -- class 903: alpha = 227, g = 1, beta = 226
    have hnform : n = 907 * k + 903 := by omega
    rw [hnform]
    refine ⟨227 * k + 226, 227 * (907 * k + 903), 227 * (227 * k + 226) * (907 * k + 903), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 227 * k + 226 := by nlinarith
      have hk2 : (0 : ℚ) < 907 * k + 903 := by nlinarith
      field_simp
      ring
