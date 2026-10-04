-- Prove2me | solution 1 for ErdosStraus242.family_mod751
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:28.227979+00:00
-- url     : https://prove2.me/submissions/ba9d53e2-c597-41bb-926e-655874ffc190

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 751 ∈ ({747, 743, 735, 563, 375} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 751
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 751 * k + n % 751 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h
  · -- class 747: alpha = 188, g = 1, beta = 187
    have hnform : n = 751 * k + 747 := by omega
    rw [hnform]
    refine ⟨188 * k + 187, 188 * (751 * k + 747), 188 * (188 * k + 187) * (751 * k + 747), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 188 * k + 187 := by nlinarith
      have hk2 : (0 : ℚ) < 751 * k + 747 := by nlinarith
      field_simp
      ring
  · -- class 743: alpha = 188, g = 2, beta = 186
    have hnform : n = 751 * k + 743 := by omega
    rw [hnform]
    refine ⟨188 * k + 186, 188 * (751 * k + 743), 94 * (188 * k + 186) * (751 * k + 743), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 188 * k + 186 := by nlinarith
      have hk2 : (0 : ℚ) < 751 * k + 743 := by nlinarith
      field_simp
      ring
  · -- class 735: alpha = 188, g = 4, beta = 184
    have hnform : n = 751 * k + 735 := by omega
    rw [hnform]
    refine ⟨188 * k + 184, 188 * (751 * k + 735), 47 * (188 * k + 184) * (751 * k + 735), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 188 * k + 184 := by nlinarith
      have hk2 : (0 : ℚ) < 751 * k + 735 := by nlinarith
      field_simp
      ring
  · -- class 563: alpha = 188, g = 47, beta = 141
    have hnform : n = 751 * k + 563 := by omega
    rw [hnform]
    refine ⟨188 * k + 141, 188 * (751 * k + 563), 4 * (188 * k + 141) * (751 * k + 563), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 188 * k + 141 := by nlinarith
      have hk2 : (0 : ℚ) < 751 * k + 563 := by nlinarith
      field_simp
      ring
  · -- class 375: alpha = 188, g = 94, beta = 94
    have hnform : n = 751 * k + 375 := by omega
    by_cases hk0 : k = 0
    · have h375 : n = 375 := by omega
      rw [h375]
      refine ⟨94, 35251, 1242597750, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨188 * k + 94, 188 * (751 * k + 375), 2 * (188 * k + 94) * (751 * k + 375), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 188 * k + 94 := by nlinarith
        have hk2 : (0 : ℚ) < 751 * k + 375 := by nlinarith
        field_simp
        ring
