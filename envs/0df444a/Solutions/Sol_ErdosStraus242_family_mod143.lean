-- Prove2me | solution 1 for ErdosStraus242.family_mod143
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:16:22.960735+00:00
-- url     : https://prove2.me/submissions/058f9f61-7099-462c-aa3f-e7caa2796287

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 143 ∈ ({71, 95, 107, 119, 127, 131, 135, 139} : Finset ℕ)) :
    IsErdosStraus n := by
  let k := n / 143
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 143 * k + n % 143 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h
  · -- class 71: alpha = 36, g = 18, beta = 18
    have hnform : n = 143 * k + 71 := by omega
    by_cases hk0 : k = 0
    · have h71 : n = 71 := by omega
      rw [h71]
      refine ⟨18, 1279, 1634562, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · rw [hnform]
      have hk1 : 1 ≤ k := by omega
      refine ⟨36 * k + 18, 36 * (143 * k + 71), 2 * (36 * k + 18) * (143 * k + 71), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 36 * k + 18 := by nlinarith
        have hk2 : (0 : ℚ) < 143 * k + 71 := by nlinarith
        field_simp
        ring
  · -- class 95: alpha = 36, g = 12, beta = 24
    have hnform : n = 143 * k + 95 := by omega
    rw [hnform]
    refine ⟨36 * k + 24, 36 * (143 * k + 95), 3 * (36 * k + 24) * (143 * k + 95), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 36 * k + 24 := by nlinarith
      have hk2 : (0 : ℚ) < 143 * k + 95 := by nlinarith
      field_simp
      ring
  · -- class 107: alpha = 36, g = 9, beta = 27
    have hnform : n = 143 * k + 107 := by omega
    rw [hnform]
    refine ⟨36 * k + 27, 36 * (143 * k + 107), 4 * (36 * k + 27) * (143 * k + 107), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 36 * k + 27 := by nlinarith
      have hk2 : (0 : ℚ) < 143 * k + 107 := by nlinarith
      field_simp
      ring
  · -- class 119: alpha = 36, g = 6, beta = 30
    have hnform : n = 143 * k + 119 := by omega
    rw [hnform]
    refine ⟨36 * k + 30, 36 * (143 * k + 119), 6 * (36 * k + 30) * (143 * k + 119), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 36 * k + 30 := by nlinarith
      have hk2 : (0 : ℚ) < 143 * k + 119 := by nlinarith
      field_simp
      ring
  · -- class 127: alpha = 36, g = 4, beta = 32
    have hnform : n = 143 * k + 127 := by omega
    rw [hnform]
    refine ⟨36 * k + 32, 36 * (143 * k + 127), 9 * (36 * k + 32) * (143 * k + 127), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 36 * k + 32 := by nlinarith
      have hk2 : (0 : ℚ) < 143 * k + 127 := by nlinarith
      field_simp
      ring
  · -- class 131: alpha = 36, g = 3, beta = 33
    have hnform : n = 143 * k + 131 := by omega
    rw [hnform]
    refine ⟨36 * k + 33, 36 * (143 * k + 131), 12 * (36 * k + 33) * (143 * k + 131), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 36 * k + 33 := by nlinarith
      have hk2 : (0 : ℚ) < 143 * k + 131 := by nlinarith
      field_simp
      ring
  · -- class 135: alpha = 36, g = 2, beta = 34
    have hnform : n = 143 * k + 135 := by omega
    rw [hnform]
    refine ⟨36 * k + 34, 36 * (143 * k + 135), 18 * (36 * k + 34) * (143 * k + 135), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 36 * k + 34 := by nlinarith
      have hk2 : (0 : ℚ) < 143 * k + 135 := by nlinarith
      field_simp
      ring
  · -- class 139: alpha = 36, g = 1, beta = 35
    have hnform : n = 143 * k + 139 := by omega
    rw [hnform]
    refine ⟨36 * k + 35, 36 * (143 * k + 139), 36 * (36 * k + 35) * (143 * k + 139), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 36 * k + 35 := by nlinarith
      have hk2 : (0 : ℚ) < 143 * k + 139 := by nlinarith
      field_simp
      ring
