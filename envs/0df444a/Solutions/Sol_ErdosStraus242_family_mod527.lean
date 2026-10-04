-- Prove2me | solution 1 for ErdosStraus242.family_mod527
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:36.517545+00:00
-- url     : https://prove2.me/submissions/34aaf301-6491-4e6a-8ed4-7fa394fd03db

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 527 ∈ ({523, 519, 515, 511, 503, 483, 479, 439, 395, 351, 263} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 527
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 527 * k + n % 527 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h
  · -- class 523: alpha = 132, g = 1, beta = 131
    have hnform : n = 527 * k + 523 := by omega
    rw [hnform]
    refine ⟨132 * k + 131, 132 * (527 * k + 523), 132 * (132 * k + 131) * (527 * k + 523), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 132 * k + 131 := by nlinarith
      have hk2 : (0 : ℚ) < 527 * k + 523 := by nlinarith
      field_simp
      ring
  · -- class 519: alpha = 132, g = 2, beta = 130
    have hnform : n = 527 * k + 519 := by omega
    rw [hnform]
    refine ⟨132 * k + 130, 132 * (527 * k + 519), 66 * (132 * k + 130) * (527 * k + 519), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 132 * k + 130 := by nlinarith
      have hk2 : (0 : ℚ) < 527 * k + 519 := by nlinarith
      field_simp
      ring
  · -- class 515: alpha = 132, g = 3, beta = 129
    have hnform : n = 527 * k + 515 := by omega
    rw [hnform]
    refine ⟨132 * k + 129, 132 * (527 * k + 515), 44 * (132 * k + 129) * (527 * k + 515), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 132 * k + 129 := by nlinarith
      have hk2 : (0 : ℚ) < 527 * k + 515 := by nlinarith
      field_simp
      ring
  · -- class 511: alpha = 132, g = 4, beta = 128
    have hnform : n = 527 * k + 511 := by omega
    rw [hnform]
    refine ⟨132 * k + 128, 132 * (527 * k + 511), 33 * (132 * k + 128) * (527 * k + 511), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 132 * k + 128 := by nlinarith
      have hk2 : (0 : ℚ) < 527 * k + 511 := by nlinarith
      field_simp
      ring
  · -- class 503: alpha = 132, g = 6, beta = 126
    have hnform : n = 527 * k + 503 := by omega
    rw [hnform]
    refine ⟨132 * k + 126, 132 * (527 * k + 503), 22 * (132 * k + 126) * (527 * k + 503), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 132 * k + 126 := by nlinarith
      have hk2 : (0 : ℚ) < 527 * k + 503 := by nlinarith
      field_simp
      ring
  · -- class 483: alpha = 132, g = 11, beta = 121
    have hnform : n = 527 * k + 483 := by omega
    rw [hnform]
    refine ⟨132 * k + 121, 132 * (527 * k + 483), 12 * (132 * k + 121) * (527 * k + 483), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 132 * k + 121 := by nlinarith
      have hk2 : (0 : ℚ) < 527 * k + 483 := by nlinarith
      field_simp
      ring
  · -- class 479: alpha = 132, g = 12, beta = 120
    have hnform : n = 527 * k + 479 := by omega
    rw [hnform]
    refine ⟨132 * k + 120, 132 * (527 * k + 479), 11 * (132 * k + 120) * (527 * k + 479), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 132 * k + 120 := by nlinarith
      have hk2 : (0 : ℚ) < 527 * k + 479 := by nlinarith
      field_simp
      ring
  · -- class 439: alpha = 132, g = 22, beta = 110
    have hnform : n = 527 * k + 439 := by omega
    rw [hnform]
    refine ⟨132 * k + 110, 132 * (527 * k + 439), 6 * (132 * k + 110) * (527 * k + 439), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 132 * k + 110 := by nlinarith
      have hk2 : (0 : ℚ) < 527 * k + 439 := by nlinarith
      field_simp
      ring
  · -- class 395: alpha = 132, g = 33, beta = 99
    have hnform : n = 527 * k + 395 := by omega
    rw [hnform]
    refine ⟨132 * k + 99, 132 * (527 * k + 395), 4 * (132 * k + 99) * (527 * k + 395), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 132 * k + 99 := by nlinarith
      have hk2 : (0 : ℚ) < 527 * k + 395 := by nlinarith
      field_simp
      ring
  · -- class 351: alpha = 132, g = 44, beta = 88
    have hnform : n = 527 * k + 351 := by omega
    rw [hnform]
    refine ⟨132 * k + 88, 132 * (527 * k + 351), 3 * (132 * k + 88) * (527 * k + 351), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 132 * k + 88 := by nlinarith
      have hk2 : (0 : ℚ) < 527 * k + 351 := by nlinarith
      field_simp
      ring
  · -- class 263: alpha = 132, g = 66, beta = 66
    have hnform : n = 527 * k + 263 := by omega
    by_cases hk0 : k = 0
    · have h263 : n = 263 := by omega
      rw [h263]
      refine ⟨66, 17359, 301317522, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨132 * k + 66, 132 * (527 * k + 263), 2 * (132 * k + 66) * (527 * k + 263), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 132 * k + 66 := by nlinarith
        have hk2 : (0 : ℚ) < 527 * k + 263 := by nlinarith
        field_simp
        ring
