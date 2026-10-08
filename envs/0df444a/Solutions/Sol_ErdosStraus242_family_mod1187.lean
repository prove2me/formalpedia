-- Prove2me | solution 1 for ErdosStraus242.family_mod1187
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:44.70432+00:00
-- url     : https://prove2.me/submissions/157f01e8-a74b-4239-b74d-086568f00c65

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1187 ∈ ({1183, 1175, 1151, 1143, 1079, 1055, 791} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1187
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1187 * k + n % 1187 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 1183: alpha = 297, g = 1, beta = 296
    have hnform : n = 1187 * k + 1183 := by omega
    rw [hnform]
    refine ⟨297 * k + 296, 297 * (1187 * k + 1183), 297 * (297 * k + 296) * (1187 * k + 1183), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 297 * k + 296 := by nlinarith
      have hk2 : (0 : ℚ) < 1187 * k + 1183 := by nlinarith
      field_simp
      ring
  · -- class 1175: alpha = 297, g = 3, beta = 294
    have hnform : n = 1187 * k + 1175 := by omega
    rw [hnform]
    refine ⟨297 * k + 294, 297 * (1187 * k + 1175), 99 * (297 * k + 294) * (1187 * k + 1175), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 297 * k + 294 := by nlinarith
      have hk2 : (0 : ℚ) < 1187 * k + 1175 := by nlinarith
      field_simp
      ring
  · -- class 1151: alpha = 297, g = 9, beta = 288
    have hnform : n = 1187 * k + 1151 := by omega
    rw [hnform]
    refine ⟨297 * k + 288, 297 * (1187 * k + 1151), 33 * (297 * k + 288) * (1187 * k + 1151), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 297 * k + 288 := by nlinarith
      have hk2 : (0 : ℚ) < 1187 * k + 1151 := by nlinarith
      field_simp
      ring
  · -- class 1143: alpha = 297, g = 11, beta = 286
    have hnform : n = 1187 * k + 1143 := by omega
    rw [hnform]
    refine ⟨297 * k + 286, 297 * (1187 * k + 1143), 27 * (297 * k + 286) * (1187 * k + 1143), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 297 * k + 286 := by nlinarith
      have hk2 : (0 : ℚ) < 1187 * k + 1143 := by nlinarith
      field_simp
      ring
  · -- class 1079: alpha = 297, g = 27, beta = 270
    have hnform : n = 1187 * k + 1079 := by omega
    rw [hnform]
    refine ⟨297 * k + 270, 297 * (1187 * k + 1079), 11 * (297 * k + 270) * (1187 * k + 1079), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 297 * k + 270 := by nlinarith
      have hk2 : (0 : ℚ) < 1187 * k + 1079 := by nlinarith
      field_simp
      ring
  · -- class 1055: alpha = 297, g = 33, beta = 264
    have hnform : n = 1187 * k + 1055 := by omega
    rw [hnform]
    refine ⟨297 * k + 264, 297 * (1187 * k + 1055), 9 * (297 * k + 264) * (1187 * k + 1055), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 297 * k + 264 := by nlinarith
      have hk2 : (0 : ℚ) < 1187 * k + 1055 := by nlinarith
      field_simp
      ring
  · -- class 791: alpha = 297, g = 99, beta = 198
    have hnform : n = 1187 * k + 791 := by omega
    rw [hnform]
    refine ⟨297 * k + 198, 297 * (1187 * k + 791), 3 * (297 * k + 198) * (1187 * k + 791), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 297 * k + 198 := by nlinarith
      have hk2 : (0 : ℚ) < 1187 * k + 791 := by nlinarith
      field_simp
      ring
