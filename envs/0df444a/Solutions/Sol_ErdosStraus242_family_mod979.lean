-- Prove2me | solution 1 for ErdosStraus242.family_mod979
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:13:07.012861+00:00
-- url     : https://prove2.me/submissions/b00d49b3-f480-4450-9fb8-a162ff9e104a

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 979 ∈ ({975, 959, 951, 839, 783} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 979
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 979 * k + n % 979 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h
  · -- class 975: alpha = 245, g = 1, beta = 244
    have hnform : n = 979 * k + 975 := by omega
    rw [hnform]
    refine ⟨245 * k + 244, 245 * (979 * k + 975), 245 * (245 * k + 244) * (979 * k + 975), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 245 * k + 244 := by nlinarith
      have hk2 : (0 : ℚ) < 979 * k + 975 := by nlinarith
      field_simp
      ring
  · -- class 959: alpha = 245, g = 5, beta = 240
    have hnform : n = 979 * k + 959 := by omega
    rw [hnform]
    refine ⟨245 * k + 240, 245 * (979 * k + 959), 49 * (245 * k + 240) * (979 * k + 959), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 245 * k + 240 := by nlinarith
      have hk2 : (0 : ℚ) < 979 * k + 959 := by nlinarith
      field_simp
      ring
  · -- class 951: alpha = 245, g = 7, beta = 238
    have hnform : n = 979 * k + 951 := by omega
    rw [hnform]
    refine ⟨245 * k + 238, 245 * (979 * k + 951), 35 * (245 * k + 238) * (979 * k + 951), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 245 * k + 238 := by nlinarith
      have hk2 : (0 : ℚ) < 979 * k + 951 := by nlinarith
      field_simp
      ring
  · -- class 839: alpha = 245, g = 35, beta = 210
    have hnform : n = 979 * k + 839 := by omega
    rw [hnform]
    refine ⟨245 * k + 210, 245 * (979 * k + 839), 7 * (245 * k + 210) * (979 * k + 839), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 245 * k + 210 := by nlinarith
      have hk2 : (0 : ℚ) < 979 * k + 839 := by nlinarith
      field_simp
      ring
  · -- class 783: alpha = 245, g = 49, beta = 196
    have hnform : n = 979 * k + 783 := by omega
    rw [hnform]
    refine ⟨245 * k + 196, 245 * (979 * k + 783), 5 * (245 * k + 196) * (979 * k + 783), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 245 * k + 196 := by nlinarith
      have hk2 : (0 : ℚ) < 979 * k + 783 := by nlinarith
      field_simp
      ring
