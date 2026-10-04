-- Prove2me | solution 1 for ErdosStraus242.family_mod127
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:39:40.401444+00:00
-- url     : https://prove2.me/submissions/6796c7e4-267f-483d-b619-cab3a9093c68

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 127 ∈ ({123, 119, 111, 95, 63} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 127
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 127 * k + n % 127 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h
  · -- class 123: alpha = 32, g = 1, beta = 31
    have hnform : n = 127 * k + 123 := by omega
    rw [hnform]
    refine ⟨32 * k + 31, 32 * (127 * k + 123), 32 * (32 * k + 31) * (127 * k + 123), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 32 * k + 31 := by nlinarith
      have hk2 : (0 : ℚ) < 127 * k + 123 := by nlinarith
      field_simp
      ring
  · -- class 119: alpha = 32, g = 2, beta = 30
    have hnform : n = 127 * k + 119 := by omega
    rw [hnform]
    refine ⟨32 * k + 30, 32 * (127 * k + 119), 16 * (32 * k + 30) * (127 * k + 119), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 32 * k + 30 := by nlinarith
      have hk2 : (0 : ℚ) < 127 * k + 119 := by nlinarith
      field_simp
      ring
  · -- class 111: alpha = 32, g = 4, beta = 28
    have hnform : n = 127 * k + 111 := by omega
    rw [hnform]
    refine ⟨32 * k + 28, 32 * (127 * k + 111), 8 * (32 * k + 28) * (127 * k + 111), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 32 * k + 28 := by nlinarith
      have hk2 : (0 : ℚ) < 127 * k + 111 := by nlinarith
      field_simp
      ring
  · -- class 95: alpha = 32, g = 8, beta = 24
    have hnform : n = 127 * k + 95 := by omega
    rw [hnform]
    refine ⟨32 * k + 24, 32 * (127 * k + 95), 4 * (32 * k + 24) * (127 * k + 95), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 32 * k + 24 := by nlinarith
      have hk2 : (0 : ℚ) < 127 * k + 95 := by nlinarith
      field_simp
      ring
  · -- class 63: alpha = 32, g = 16, beta = 16
    have hnform : n = 127 * k + 63 := by omega
    by_cases hk0 : k = 0
    · have h63 : n = 63 := by omega
      rw [h63]
      refine ⟨16, 1009, 1017072, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨32 * k + 16, 32 * (127 * k + 63), 2 * (32 * k + 16) * (127 * k + 63), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 32 * k + 16 := by nlinarith
        have hk2 : (0 : ℚ) < 127 * k + 63 := by nlinarith
        field_simp
        ring
