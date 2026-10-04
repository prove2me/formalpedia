-- Prove2me | solution 1 for ErdosStraus242.family_mod299
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:44:34.463231+00:00
-- url     : https://prove2.me/submissions/0e16218a-7e13-483a-a5cd-6a4ac7c5c1b9

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 299 ∈ ({295, 287, 279, 239, 199} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 299
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 299 * k + n % 299 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h
  · -- class 295: alpha = 75, g = 1, beta = 74
    have hnform : n = 299 * k + 295 := by omega
    rw [hnform]
    refine ⟨75 * k + 74, 75 * (299 * k + 295), 75 * (75 * k + 74) * (299 * k + 295), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 75 * k + 74 := by nlinarith
      have hk2 : (0 : ℚ) < 299 * k + 295 := by nlinarith
      field_simp
      ring
  · -- class 287: alpha = 75, g = 3, beta = 72
    have hnform : n = 299 * k + 287 := by omega
    rw [hnform]
    refine ⟨75 * k + 72, 75 * (299 * k + 287), 25 * (75 * k + 72) * (299 * k + 287), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 75 * k + 72 := by nlinarith
      have hk2 : (0 : ℚ) < 299 * k + 287 := by nlinarith
      field_simp
      ring
  · -- class 279: alpha = 75, g = 5, beta = 70
    have hnform : n = 299 * k + 279 := by omega
    rw [hnform]
    refine ⟨75 * k + 70, 75 * (299 * k + 279), 15 * (75 * k + 70) * (299 * k + 279), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 75 * k + 70 := by nlinarith
      have hk2 : (0 : ℚ) < 299 * k + 279 := by nlinarith
      field_simp
      ring
  · -- class 239: alpha = 75, g = 15, beta = 60
    have hnform : n = 299 * k + 239 := by omega
    rw [hnform]
    refine ⟨75 * k + 60, 75 * (299 * k + 239), 5 * (75 * k + 60) * (299 * k + 239), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 75 * k + 60 := by nlinarith
      have hk2 : (0 : ℚ) < 299 * k + 239 := by nlinarith
      field_simp
      ring
  · -- class 199: alpha = 75, g = 25, beta = 50
    have hnform : n = 299 * k + 199 := by omega
    rw [hnform]
    refine ⟨75 * k + 50, 75 * (299 * k + 199), 3 * (75 * k + 50) * (299 * k + 199), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 75 * k + 50 := by nlinarith
      have hk2 : (0 : ℚ) < 299 * k + 199 := by nlinarith
      field_simp
      ring
