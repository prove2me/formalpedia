-- Prove2me | solution 1 for ErdosStraus242.family_mod1063
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:37.426855+00:00
-- url     : https://prove2.me/submissions/f17b4439-4ff6-405d-bfbb-f15682440586

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1063 ∈ ({1059, 1055, 1035, 1007, 987, 911, 531} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1063
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1063 * k + n % 1063 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 1059: alpha = 266, g = 1, beta = 265
    have hnform : n = 1063 * k + 1059 := by omega
    rw [hnform]
    refine ⟨266 * k + 265, 266 * (1063 * k + 1059), 266 * (266 * k + 265) * (1063 * k + 1059), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 266 * k + 265 := by nlinarith
      have hk2 : (0 : ℚ) < 1063 * k + 1059 := by nlinarith
      field_simp
      ring
  · -- class 1055: alpha = 266, g = 2, beta = 264
    have hnform : n = 1063 * k + 1055 := by omega
    rw [hnform]
    refine ⟨266 * k + 264, 266 * (1063 * k + 1055), 133 * (266 * k + 264) * (1063 * k + 1055), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 266 * k + 264 := by nlinarith
      have hk2 : (0 : ℚ) < 1063 * k + 1055 := by nlinarith
      field_simp
      ring
  · -- class 1035: alpha = 266, g = 7, beta = 259
    have hnform : n = 1063 * k + 1035 := by omega
    rw [hnform]
    refine ⟨266 * k + 259, 266 * (1063 * k + 1035), 38 * (266 * k + 259) * (1063 * k + 1035), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 266 * k + 259 := by nlinarith
      have hk2 : (0 : ℚ) < 1063 * k + 1035 := by nlinarith
      field_simp
      ring
  · -- class 1007: alpha = 266, g = 14, beta = 252
    have hnform : n = 1063 * k + 1007 := by omega
    rw [hnform]
    refine ⟨266 * k + 252, 266 * (1063 * k + 1007), 19 * (266 * k + 252) * (1063 * k + 1007), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 266 * k + 252 := by nlinarith
      have hk2 : (0 : ℚ) < 1063 * k + 1007 := by nlinarith
      field_simp
      ring
  · -- class 987: alpha = 266, g = 19, beta = 247
    have hnform : n = 1063 * k + 987 := by omega
    rw [hnform]
    refine ⟨266 * k + 247, 266 * (1063 * k + 987), 14 * (266 * k + 247) * (1063 * k + 987), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 266 * k + 247 := by nlinarith
      have hk2 : (0 : ℚ) < 1063 * k + 987 := by nlinarith
      field_simp
      ring
  · -- class 911: alpha = 266, g = 38, beta = 228
    have hnform : n = 1063 * k + 911 := by omega
    rw [hnform]
    refine ⟨266 * k + 228, 266 * (1063 * k + 911), 7 * (266 * k + 228) * (1063 * k + 911), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 266 * k + 228 := by nlinarith
      have hk2 : (0 : ℚ) < 1063 * k + 911 := by nlinarith
      field_simp
      ring
  · -- class 531: alpha = 266, g = 133, beta = 133
    have hnform : n = 1063 * k + 531 := by omega
    by_cases hk0 : k = 0
    · have h531 : n = 531 := by omega
      rw [h531]
      refine ⟨133, 70624, 4987678752, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨266 * k + 133, 266 * (1063 * k + 531), 2 * (266 * k + 133) * (1063 * k + 531), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 266 * k + 133 := by nlinarith
        have hk2 : (0 : ℚ) < 1063 * k + 531 := by nlinarith
        field_simp
        ring
