-- Prove2me | solution 1 for ErdosStraus242.family_mod1163
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:43.702116+00:00
-- url     : https://prove2.me/submissions/3c2a0fd7-30cc-43c2-9365-b1aa021ca9ec

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1163 ∈ ({1159, 1151, 775} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1163
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1163 * k + n % 1163 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 1159: alpha = 291, g = 1, beta = 290
    have hnform : n = 1163 * k + 1159 := by omega
    rw [hnform]
    refine ⟨291 * k + 290, 291 * (1163 * k + 1159), 291 * (291 * k + 290) * (1163 * k + 1159), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 291 * k + 290 := by nlinarith
      have hk2 : (0 : ℚ) < 1163 * k + 1159 := by nlinarith
      field_simp
      ring
  · -- class 1151: alpha = 291, g = 3, beta = 288
    have hnform : n = 1163 * k + 1151 := by omega
    rw [hnform]
    refine ⟨291 * k + 288, 291 * (1163 * k + 1151), 97 * (291 * k + 288) * (1163 * k + 1151), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 291 * k + 288 := by nlinarith
      have hk2 : (0 : ℚ) < 1163 * k + 1151 := by nlinarith
      field_simp
      ring
  · -- class 775: alpha = 291, g = 97, beta = 194
    have hnform : n = 1163 * k + 775 := by omega
    rw [hnform]
    refine ⟨291 * k + 194, 291 * (1163 * k + 775), 3 * (291 * k + 194) * (1163 * k + 775), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 291 * k + 194 := by nlinarith
      have hk2 : (0 : ℚ) < 1163 * k + 775 := by nlinarith
      field_simp
      ring
