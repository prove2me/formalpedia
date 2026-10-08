-- Prove2me | solution 1 for ErdosStraus242.family_mod899
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:13:01.438836+00:00
-- url     : https://prove2.me/submissions/13de74ac-f61d-47f5-9764-1e12dca33c87

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 899 ∈ ({895, 887, 879, 863, 839, 799, 719, 599} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 899
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 899 * k + n % 899 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h
  · -- class 895: alpha = 225, g = 1, beta = 224
    have hnform : n = 899 * k + 895 := by omega
    rw [hnform]
    refine ⟨225 * k + 224, 225 * (899 * k + 895), 225 * (225 * k + 224) * (899 * k + 895), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 225 * k + 224 := by nlinarith
      have hk2 : (0 : ℚ) < 899 * k + 895 := by nlinarith
      field_simp
      ring
  · -- class 887: alpha = 225, g = 3, beta = 222
    have hnform : n = 899 * k + 887 := by omega
    rw [hnform]
    refine ⟨225 * k + 222, 225 * (899 * k + 887), 75 * (225 * k + 222) * (899 * k + 887), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 225 * k + 222 := by nlinarith
      have hk2 : (0 : ℚ) < 899 * k + 887 := by nlinarith
      field_simp
      ring
  · -- class 879: alpha = 225, g = 5, beta = 220
    have hnform : n = 899 * k + 879 := by omega
    rw [hnform]
    refine ⟨225 * k + 220, 225 * (899 * k + 879), 45 * (225 * k + 220) * (899 * k + 879), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 225 * k + 220 := by nlinarith
      have hk2 : (0 : ℚ) < 899 * k + 879 := by nlinarith
      field_simp
      ring
  · -- class 863: alpha = 225, g = 9, beta = 216
    have hnform : n = 899 * k + 863 := by omega
    rw [hnform]
    refine ⟨225 * k + 216, 225 * (899 * k + 863), 25 * (225 * k + 216) * (899 * k + 863), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 225 * k + 216 := by nlinarith
      have hk2 : (0 : ℚ) < 899 * k + 863 := by nlinarith
      field_simp
      ring
  · -- class 839: alpha = 225, g = 15, beta = 210
    have hnform : n = 899 * k + 839 := by omega
    rw [hnform]
    refine ⟨225 * k + 210, 225 * (899 * k + 839), 15 * (225 * k + 210) * (899 * k + 839), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 225 * k + 210 := by nlinarith
      have hk2 : (0 : ℚ) < 899 * k + 839 := by nlinarith
      field_simp
      ring
  · -- class 799: alpha = 225, g = 25, beta = 200
    have hnform : n = 899 * k + 799 := by omega
    rw [hnform]
    refine ⟨225 * k + 200, 225 * (899 * k + 799), 9 * (225 * k + 200) * (899 * k + 799), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 225 * k + 200 := by nlinarith
      have hk2 : (0 : ℚ) < 899 * k + 799 := by nlinarith
      field_simp
      ring
  · -- class 719: alpha = 225, g = 45, beta = 180
    have hnform : n = 899 * k + 719 := by omega
    rw [hnform]
    refine ⟨225 * k + 180, 225 * (899 * k + 719), 5 * (225 * k + 180) * (899 * k + 719), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 225 * k + 180 := by nlinarith
      have hk2 : (0 : ℚ) < 899 * k + 719 := by nlinarith
      field_simp
      ring
  · -- class 599: alpha = 225, g = 75, beta = 150
    have hnform : n = 899 * k + 599 := by omega
    rw [hnform]
    refine ⟨225 * k + 150, 225 * (899 * k + 599), 3 * (225 * k + 150) * (899 * k + 599), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 225 * k + 150 := by nlinarith
      have hk2 : (0 : ℚ) < 899 * k + 599 := by nlinarith
      field_simp
      ring
