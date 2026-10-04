-- Prove2me | solution 1 for ErdosStraus242.family_mod103
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:39:39.774554+00:00
-- url     : https://prove2.me/submissions/7d3d9f41-1057-4a76-a66a-472a28aa8d2d

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 103 ∈ ({99, 95, 51} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 103
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 103 * k + n % 103 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 99: alpha = 26, g = 1, beta = 25
    have hnform : n = 103 * k + 99 := by omega
    rw [hnform]
    refine ⟨26 * k + 25, 26 * (103 * k + 99), 26 * (26 * k + 25) * (103 * k + 99), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 26 * k + 25 := by nlinarith
      have hk2 : (0 : ℚ) < 103 * k + 99 := by nlinarith
      field_simp
      ring
  · -- class 95: alpha = 26, g = 2, beta = 24
    have hnform : n = 103 * k + 95 := by omega
    rw [hnform]
    refine ⟨26 * k + 24, 26 * (103 * k + 95), 13 * (26 * k + 24) * (103 * k + 95), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 26 * k + 24 := by nlinarith
      have hk2 : (0 : ℚ) < 103 * k + 95 := by nlinarith
      field_simp
      ring
  · -- class 51: alpha = 26, g = 13, beta = 13
    have hnform : n = 103 * k + 51 := by omega
    by_cases hk0 : k = 0
    · have h51 : n = 51 := by omega
      rw [h51]
      refine ⟨13, 664, 440232, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨26 * k + 13, 26 * (103 * k + 51), 2 * (26 * k + 13) * (103 * k + 51), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 26 * k + 13 := by nlinarith
        have hk2 : (0 : ℚ) < 103 * k + 51 := by nlinarith
        field_simp
        ring
