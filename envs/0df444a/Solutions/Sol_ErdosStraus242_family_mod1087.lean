-- Prove2me | solution 1 for ErdosStraus242.family_mod1087
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:38.950155+00:00
-- url     : https://prove2.me/submissions/2e43e6bb-9eb2-4501-95bb-30f48989e511

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1087 ∈ ({1083, 1079, 1071, 1055, 1023, 1019, 951, 815, 543} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1087
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1087 * k + n % 1087 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h
  · -- class 1083: alpha = 272, g = 1, beta = 271
    have hnform : n = 1087 * k + 1083 := by omega
    rw [hnform]
    refine ⟨272 * k + 271, 272 * (1087 * k + 1083), 272 * (272 * k + 271) * (1087 * k + 1083), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 272 * k + 271 := by nlinarith
      have hk2 : (0 : ℚ) < 1087 * k + 1083 := by nlinarith
      field_simp
      ring
  · -- class 1079: alpha = 272, g = 2, beta = 270
    have hnform : n = 1087 * k + 1079 := by omega
    rw [hnform]
    refine ⟨272 * k + 270, 272 * (1087 * k + 1079), 136 * (272 * k + 270) * (1087 * k + 1079), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 272 * k + 270 := by nlinarith
      have hk2 : (0 : ℚ) < 1087 * k + 1079 := by nlinarith
      field_simp
      ring
  · -- class 1071: alpha = 272, g = 4, beta = 268
    have hnform : n = 1087 * k + 1071 := by omega
    rw [hnform]
    refine ⟨272 * k + 268, 272 * (1087 * k + 1071), 68 * (272 * k + 268) * (1087 * k + 1071), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 272 * k + 268 := by nlinarith
      have hk2 : (0 : ℚ) < 1087 * k + 1071 := by nlinarith
      field_simp
      ring
  · -- class 1055: alpha = 272, g = 8, beta = 264
    have hnform : n = 1087 * k + 1055 := by omega
    rw [hnform]
    refine ⟨272 * k + 264, 272 * (1087 * k + 1055), 34 * (272 * k + 264) * (1087 * k + 1055), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 272 * k + 264 := by nlinarith
      have hk2 : (0 : ℚ) < 1087 * k + 1055 := by nlinarith
      field_simp
      ring
  · -- class 1023: alpha = 272, g = 16, beta = 256
    have hnform : n = 1087 * k + 1023 := by omega
    rw [hnform]
    refine ⟨272 * k + 256, 272 * (1087 * k + 1023), 17 * (272 * k + 256) * (1087 * k + 1023), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 272 * k + 256 := by nlinarith
      have hk2 : (0 : ℚ) < 1087 * k + 1023 := by nlinarith
      field_simp
      ring
  · -- class 1019: alpha = 272, g = 17, beta = 255
    have hnform : n = 1087 * k + 1019 := by omega
    rw [hnform]
    refine ⟨272 * k + 255, 272 * (1087 * k + 1019), 16 * (272 * k + 255) * (1087 * k + 1019), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 272 * k + 255 := by nlinarith
      have hk2 : (0 : ℚ) < 1087 * k + 1019 := by nlinarith
      field_simp
      ring
  · -- class 951: alpha = 272, g = 34, beta = 238
    have hnform : n = 1087 * k + 951 := by omega
    rw [hnform]
    refine ⟨272 * k + 238, 272 * (1087 * k + 951), 8 * (272 * k + 238) * (1087 * k + 951), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 272 * k + 238 := by nlinarith
      have hk2 : (0 : ℚ) < 1087 * k + 951 := by nlinarith
      field_simp
      ring
  · -- class 815: alpha = 272, g = 68, beta = 204
    have hnform : n = 1087 * k + 815 := by omega
    rw [hnform]
    refine ⟨272 * k + 204, 272 * (1087 * k + 815), 4 * (272 * k + 204) * (1087 * k + 815), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 272 * k + 204 := by nlinarith
      have hk2 : (0 : ℚ) < 1087 * k + 815 := by nlinarith
      field_simp
      ring
  · -- class 543: alpha = 272, g = 136, beta = 136
    have hnform : n = 1087 * k + 543 := by omega
    by_cases hk0 : k = 0
    · have h543 : n = 543 := by omega
      rw [h543]
      refine ⟨136, 73849, 5453600952, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨272 * k + 136, 272 * (1087 * k + 543), 2 * (272 * k + 136) * (1087 * k + 543), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 272 * k + 136 := by nlinarith
        have hk2 : (0 : ℚ) < 1087 * k + 543 := by nlinarith
        field_simp
        ring
