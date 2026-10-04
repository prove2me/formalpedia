-- Prove2me | solution 1 for ErdosStraus242.family_mod671
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:05.150341+00:00
-- url     : https://prove2.me/submissions/15351453-5647-4745-af51-9c30f27fefc3

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 671 ∈ ({667, 663, 659, 655, 647, 643, 639, 623, 615, 587, 575, 559, 503, 447, 335} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 671
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 671 * k + n % 671 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · -- class 667: alpha = 168, g = 1, beta = 167
    have hnform : n = 671 * k + 667 := by omega
    rw [hnform]
    refine ⟨168 * k + 167, 168 * (671 * k + 667), 168 * (168 * k + 167) * (671 * k + 667), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 168 * k + 167 := by nlinarith
      have hk2 : (0 : ℚ) < 671 * k + 667 := by nlinarith
      field_simp
      ring
  · -- class 663: alpha = 168, g = 2, beta = 166
    have hnform : n = 671 * k + 663 := by omega
    rw [hnform]
    refine ⟨168 * k + 166, 168 * (671 * k + 663), 84 * (168 * k + 166) * (671 * k + 663), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 168 * k + 166 := by nlinarith
      have hk2 : (0 : ℚ) < 671 * k + 663 := by nlinarith
      field_simp
      ring
  · -- class 659: alpha = 168, g = 3, beta = 165
    have hnform : n = 671 * k + 659 := by omega
    rw [hnform]
    refine ⟨168 * k + 165, 168 * (671 * k + 659), 56 * (168 * k + 165) * (671 * k + 659), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 168 * k + 165 := by nlinarith
      have hk2 : (0 : ℚ) < 671 * k + 659 := by nlinarith
      field_simp
      ring
  · -- class 655: alpha = 168, g = 4, beta = 164
    have hnform : n = 671 * k + 655 := by omega
    rw [hnform]
    refine ⟨168 * k + 164, 168 * (671 * k + 655), 42 * (168 * k + 164) * (671 * k + 655), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 168 * k + 164 := by nlinarith
      have hk2 : (0 : ℚ) < 671 * k + 655 := by nlinarith
      field_simp
      ring
  · -- class 647: alpha = 168, g = 6, beta = 162
    have hnform : n = 671 * k + 647 := by omega
    rw [hnform]
    refine ⟨168 * k + 162, 168 * (671 * k + 647), 28 * (168 * k + 162) * (671 * k + 647), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 168 * k + 162 := by nlinarith
      have hk2 : (0 : ℚ) < 671 * k + 647 := by nlinarith
      field_simp
      ring
  · -- class 643: alpha = 168, g = 7, beta = 161
    have hnform : n = 671 * k + 643 := by omega
    rw [hnform]
    refine ⟨168 * k + 161, 168 * (671 * k + 643), 24 * (168 * k + 161) * (671 * k + 643), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 168 * k + 161 := by nlinarith
      have hk2 : (0 : ℚ) < 671 * k + 643 := by nlinarith
      field_simp
      ring
  · -- class 639: alpha = 168, g = 8, beta = 160
    have hnform : n = 671 * k + 639 := by omega
    rw [hnform]
    refine ⟨168 * k + 160, 168 * (671 * k + 639), 21 * (168 * k + 160) * (671 * k + 639), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 168 * k + 160 := by nlinarith
      have hk2 : (0 : ℚ) < 671 * k + 639 := by nlinarith
      field_simp
      ring
  · -- class 623: alpha = 168, g = 12, beta = 156
    have hnform : n = 671 * k + 623 := by omega
    rw [hnform]
    refine ⟨168 * k + 156, 168 * (671 * k + 623), 14 * (168 * k + 156) * (671 * k + 623), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 168 * k + 156 := by nlinarith
      have hk2 : (0 : ℚ) < 671 * k + 623 := by nlinarith
      field_simp
      ring
  · -- class 615: alpha = 168, g = 14, beta = 154
    have hnform : n = 671 * k + 615 := by omega
    rw [hnform]
    refine ⟨168 * k + 154, 168 * (671 * k + 615), 12 * (168 * k + 154) * (671 * k + 615), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 168 * k + 154 := by nlinarith
      have hk2 : (0 : ℚ) < 671 * k + 615 := by nlinarith
      field_simp
      ring
  · -- class 587: alpha = 168, g = 21, beta = 147
    have hnform : n = 671 * k + 587 := by omega
    rw [hnform]
    refine ⟨168 * k + 147, 168 * (671 * k + 587), 8 * (168 * k + 147) * (671 * k + 587), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 168 * k + 147 := by nlinarith
      have hk2 : (0 : ℚ) < 671 * k + 587 := by nlinarith
      field_simp
      ring
  · -- class 575: alpha = 168, g = 24, beta = 144
    have hnform : n = 671 * k + 575 := by omega
    rw [hnform]
    refine ⟨168 * k + 144, 168 * (671 * k + 575), 7 * (168 * k + 144) * (671 * k + 575), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 168 * k + 144 := by nlinarith
      have hk2 : (0 : ℚ) < 671 * k + 575 := by nlinarith
      field_simp
      ring
  · -- class 559: alpha = 168, g = 28, beta = 140
    have hnform : n = 671 * k + 559 := by omega
    rw [hnform]
    refine ⟨168 * k + 140, 168 * (671 * k + 559), 6 * (168 * k + 140) * (671 * k + 559), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 168 * k + 140 := by nlinarith
      have hk2 : (0 : ℚ) < 671 * k + 559 := by nlinarith
      field_simp
      ring
  · -- class 503: alpha = 168, g = 42, beta = 126
    have hnform : n = 671 * k + 503 := by omega
    rw [hnform]
    refine ⟨168 * k + 126, 168 * (671 * k + 503), 4 * (168 * k + 126) * (671 * k + 503), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 168 * k + 126 := by nlinarith
      have hk2 : (0 : ℚ) < 671 * k + 503 := by nlinarith
      field_simp
      ring
  · -- class 447: alpha = 168, g = 56, beta = 112
    have hnform : n = 671 * k + 447 := by omega
    rw [hnform]
    refine ⟨168 * k + 112, 168 * (671 * k + 447), 3 * (168 * k + 112) * (671 * k + 447), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 168 * k + 112 := by nlinarith
      have hk2 : (0 : ℚ) < 671 * k + 447 := by nlinarith
      field_simp
      ring
  · -- class 335: alpha = 168, g = 84, beta = 84
    have hnform : n = 671 * k + 335 := by omega
    by_cases hk0 : k = 0
    · have h335 : n = 335 := by omega
      rw [h335]
      refine ⟨84, 28141, 791887740, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨168 * k + 84, 168 * (671 * k + 335), 2 * (168 * k + 84) * (671 * k + 335), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 168 * k + 84 := by nlinarith
        have hk2 : (0 : ℚ) < 671 * k + 335 := by nlinarith
        field_simp
        ring
