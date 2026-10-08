-- Prove2me | solution 1 for ErdosStraus242.family_mod1019
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:34.937331+00:00
-- url     : https://prove2.me/submissions/acb28f01-4b2f-4524-b8ae-f05aef78d2ba

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1019 ∈ ({1015, 1007, 999, 959, 951, 815, 679} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1019
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1019 * k + n % 1019 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 1015: alpha = 255, g = 1, beta = 254
    have hnform : n = 1019 * k + 1015 := by omega
    rw [hnform]
    refine ⟨255 * k + 254, 255 * (1019 * k + 1015), 255 * (255 * k + 254) * (1019 * k + 1015), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 255 * k + 254 := by nlinarith
      have hk2 : (0 : ℚ) < 1019 * k + 1015 := by nlinarith
      field_simp
      ring
  · -- class 1007: alpha = 255, g = 3, beta = 252
    have hnform : n = 1019 * k + 1007 := by omega
    rw [hnform]
    refine ⟨255 * k + 252, 255 * (1019 * k + 1007), 85 * (255 * k + 252) * (1019 * k + 1007), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 255 * k + 252 := by nlinarith
      have hk2 : (0 : ℚ) < 1019 * k + 1007 := by nlinarith
      field_simp
      ring
  · -- class 999: alpha = 255, g = 5, beta = 250
    have hnform : n = 1019 * k + 999 := by omega
    rw [hnform]
    refine ⟨255 * k + 250, 255 * (1019 * k + 999), 51 * (255 * k + 250) * (1019 * k + 999), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 255 * k + 250 := by nlinarith
      have hk2 : (0 : ℚ) < 1019 * k + 999 := by nlinarith
      field_simp
      ring
  · -- class 959: alpha = 255, g = 15, beta = 240
    have hnform : n = 1019 * k + 959 := by omega
    rw [hnform]
    refine ⟨255 * k + 240, 255 * (1019 * k + 959), 17 * (255 * k + 240) * (1019 * k + 959), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 255 * k + 240 := by nlinarith
      have hk2 : (0 : ℚ) < 1019 * k + 959 := by nlinarith
      field_simp
      ring
  · -- class 951: alpha = 255, g = 17, beta = 238
    have hnform : n = 1019 * k + 951 := by omega
    rw [hnform]
    refine ⟨255 * k + 238, 255 * (1019 * k + 951), 15 * (255 * k + 238) * (1019 * k + 951), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 255 * k + 238 := by nlinarith
      have hk2 : (0 : ℚ) < 1019 * k + 951 := by nlinarith
      field_simp
      ring
  · -- class 815: alpha = 255, g = 51, beta = 204
    have hnform : n = 1019 * k + 815 := by omega
    rw [hnform]
    refine ⟨255 * k + 204, 255 * (1019 * k + 815), 5 * (255 * k + 204) * (1019 * k + 815), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 255 * k + 204 := by nlinarith
      have hk2 : (0 : ℚ) < 1019 * k + 815 := by nlinarith
      field_simp
      ring
  · -- class 679: alpha = 255, g = 85, beta = 170
    have hnform : n = 1019 * k + 679 := by omega
    rw [hnform]
    refine ⟨255 * k + 170, 255 * (1019 * k + 679), 3 * (255 * k + 170) * (1019 * k + 679), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 255 * k + 170 := by nlinarith
      have hk2 : (0 : ℚ) < 1019 * k + 679 := by nlinarith
      field_simp
      ring
