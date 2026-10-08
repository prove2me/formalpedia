-- Prove2me | solution 1 for ErdosStraus242.family_mod851
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:12:57.31782+00:00
-- url     : https://prove2.me/submissions/54a9023f-c914-4b91-9c8a-1a9ec6b89082

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 851 ∈ ({847, 839, 567} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 851
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 851 * k + n % 851 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 847: alpha = 213, g = 1, beta = 212
    have hnform : n = 851 * k + 847 := by omega
    rw [hnform]
    refine ⟨213 * k + 212, 213 * (851 * k + 847), 213 * (213 * k + 212) * (851 * k + 847), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 213 * k + 212 := by nlinarith
      have hk2 : (0 : ℚ) < 851 * k + 847 := by nlinarith
      field_simp
      ring
  · -- class 839: alpha = 213, g = 3, beta = 210
    have hnform : n = 851 * k + 839 := by omega
    rw [hnform]
    refine ⟨213 * k + 210, 213 * (851 * k + 839), 71 * (213 * k + 210) * (851 * k + 839), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 213 * k + 210 := by nlinarith
      have hk2 : (0 : ℚ) < 851 * k + 839 := by nlinarith
      field_simp
      ring
  · -- class 567: alpha = 213, g = 71, beta = 142
    have hnform : n = 851 * k + 567 := by omega
    rw [hnform]
    refine ⟨213 * k + 142, 213 * (851 * k + 567), 3 * (213 * k + 142) * (851 * k + 567), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 213 * k + 142 := by nlinarith
      have hk2 : (0 : ℚ) < 851 * k + 567 := by nlinarith
      field_simp
      ring
