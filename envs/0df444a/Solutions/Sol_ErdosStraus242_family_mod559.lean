-- Prove2me | solution 1 for ErdosStraus242.family_mod559
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:38.395447+00:00
-- url     : https://prove2.me/submissions/ec0aa275-4b7d-4a97-ac70-7a123ceac913

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 559 ∈ ({555, 551, 543, 539, 531, 519, 503, 479, 447, 419, 279} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 559
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 559 * k + n % 559 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h
  · -- class 555: alpha = 140, g = 1, beta = 139
    have hnform : n = 559 * k + 555 := by omega
    rw [hnform]
    refine ⟨140 * k + 139, 140 * (559 * k + 555), 140 * (140 * k + 139) * (559 * k + 555), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 140 * k + 139 := by nlinarith
      have hk2 : (0 : ℚ) < 559 * k + 555 := by nlinarith
      field_simp
      ring
  · -- class 551: alpha = 140, g = 2, beta = 138
    have hnform : n = 559 * k + 551 := by omega
    rw [hnform]
    refine ⟨140 * k + 138, 140 * (559 * k + 551), 70 * (140 * k + 138) * (559 * k + 551), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 140 * k + 138 := by nlinarith
      have hk2 : (0 : ℚ) < 559 * k + 551 := by nlinarith
      field_simp
      ring
  · -- class 543: alpha = 140, g = 4, beta = 136
    have hnform : n = 559 * k + 543 := by omega
    rw [hnform]
    refine ⟨140 * k + 136, 140 * (559 * k + 543), 35 * (140 * k + 136) * (559 * k + 543), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 140 * k + 136 := by nlinarith
      have hk2 : (0 : ℚ) < 559 * k + 543 := by nlinarith
      field_simp
      ring
  · -- class 539: alpha = 140, g = 5, beta = 135
    have hnform : n = 559 * k + 539 := by omega
    rw [hnform]
    refine ⟨140 * k + 135, 140 * (559 * k + 539), 28 * (140 * k + 135) * (559 * k + 539), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 140 * k + 135 := by nlinarith
      have hk2 : (0 : ℚ) < 559 * k + 539 := by nlinarith
      field_simp
      ring
  · -- class 531: alpha = 140, g = 7, beta = 133
    have hnform : n = 559 * k + 531 := by omega
    rw [hnform]
    refine ⟨140 * k + 133, 140 * (559 * k + 531), 20 * (140 * k + 133) * (559 * k + 531), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 140 * k + 133 := by nlinarith
      have hk2 : (0 : ℚ) < 559 * k + 531 := by nlinarith
      field_simp
      ring
  · -- class 519: alpha = 140, g = 10, beta = 130
    have hnform : n = 559 * k + 519 := by omega
    rw [hnform]
    refine ⟨140 * k + 130, 140 * (559 * k + 519), 14 * (140 * k + 130) * (559 * k + 519), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 140 * k + 130 := by nlinarith
      have hk2 : (0 : ℚ) < 559 * k + 519 := by nlinarith
      field_simp
      ring
  · -- class 503: alpha = 140, g = 14, beta = 126
    have hnform : n = 559 * k + 503 := by omega
    rw [hnform]
    refine ⟨140 * k + 126, 140 * (559 * k + 503), 10 * (140 * k + 126) * (559 * k + 503), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 140 * k + 126 := by nlinarith
      have hk2 : (0 : ℚ) < 559 * k + 503 := by nlinarith
      field_simp
      ring
  · -- class 479: alpha = 140, g = 20, beta = 120
    have hnform : n = 559 * k + 479 := by omega
    rw [hnform]
    refine ⟨140 * k + 120, 140 * (559 * k + 479), 7 * (140 * k + 120) * (559 * k + 479), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 140 * k + 120 := by nlinarith
      have hk2 : (0 : ℚ) < 559 * k + 479 := by nlinarith
      field_simp
      ring
  · -- class 447: alpha = 140, g = 28, beta = 112
    have hnform : n = 559 * k + 447 := by omega
    rw [hnform]
    refine ⟨140 * k + 112, 140 * (559 * k + 447), 5 * (140 * k + 112) * (559 * k + 447), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 140 * k + 112 := by nlinarith
      have hk2 : (0 : ℚ) < 559 * k + 447 := by nlinarith
      field_simp
      ring
  · -- class 419: alpha = 140, g = 35, beta = 105
    have hnform : n = 559 * k + 419 := by omega
    rw [hnform]
    refine ⟨140 * k + 105, 140 * (559 * k + 419), 4 * (140 * k + 105) * (559 * k + 419), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 140 * k + 105 := by nlinarith
      have hk2 : (0 : ℚ) < 559 * k + 419 := by nlinarith
      field_simp
      ring
  · -- class 279: alpha = 140, g = 70, beta = 70
    have hnform : n = 559 * k + 279 := by omega
    by_cases hk0 : k = 0
    · have h279 : n = 279 := by omega
      rw [h279]
      refine ⟨70, 19531, 381440430, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨140 * k + 70, 140 * (559 * k + 279), 2 * (140 * k + 70) * (559 * k + 279), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 140 * k + 70 := by nlinarith
        have hk2 : (0 : ℚ) < 559 * k + 279 := by nlinarith
        field_simp
        ring
