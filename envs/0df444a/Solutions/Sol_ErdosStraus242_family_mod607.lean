-- Prove2me | solution 1 for ErdosStraus242.family_mod607
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:00.925791+00:00
-- url     : https://prove2.me/submissions/8da6b471-030c-4752-901d-440710e3f1cf

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 607 ∈ ({603, 599, 591, 575, 531, 455, 303} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 607
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 607 * k + n % 607 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 603: alpha = 152, g = 1, beta = 151
    have hnform : n = 607 * k + 603 := by omega
    rw [hnform]
    refine ⟨152 * k + 151, 152 * (607 * k + 603), 152 * (152 * k + 151) * (607 * k + 603), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 152 * k + 151 := by nlinarith
      have hk2 : (0 : ℚ) < 607 * k + 603 := by nlinarith
      field_simp
      ring
  · -- class 599: alpha = 152, g = 2, beta = 150
    have hnform : n = 607 * k + 599 := by omega
    rw [hnform]
    refine ⟨152 * k + 150, 152 * (607 * k + 599), 76 * (152 * k + 150) * (607 * k + 599), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 152 * k + 150 := by nlinarith
      have hk2 : (0 : ℚ) < 607 * k + 599 := by nlinarith
      field_simp
      ring
  · -- class 591: alpha = 152, g = 4, beta = 148
    have hnform : n = 607 * k + 591 := by omega
    rw [hnform]
    refine ⟨152 * k + 148, 152 * (607 * k + 591), 38 * (152 * k + 148) * (607 * k + 591), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 152 * k + 148 := by nlinarith
      have hk2 : (0 : ℚ) < 607 * k + 591 := by nlinarith
      field_simp
      ring
  · -- class 575: alpha = 152, g = 8, beta = 144
    have hnform : n = 607 * k + 575 := by omega
    rw [hnform]
    refine ⟨152 * k + 144, 152 * (607 * k + 575), 19 * (152 * k + 144) * (607 * k + 575), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 152 * k + 144 := by nlinarith
      have hk2 : (0 : ℚ) < 607 * k + 575 := by nlinarith
      field_simp
      ring
  · -- class 531: alpha = 152, g = 19, beta = 133
    have hnform : n = 607 * k + 531 := by omega
    rw [hnform]
    refine ⟨152 * k + 133, 152 * (607 * k + 531), 8 * (152 * k + 133) * (607 * k + 531), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 152 * k + 133 := by nlinarith
      have hk2 : (0 : ℚ) < 607 * k + 531 := by nlinarith
      field_simp
      ring
  · -- class 455: alpha = 152, g = 38, beta = 114
    have hnform : n = 607 * k + 455 := by omega
    rw [hnform]
    refine ⟨152 * k + 114, 152 * (607 * k + 455), 4 * (152 * k + 114) * (607 * k + 455), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 152 * k + 114 := by nlinarith
      have hk2 : (0 : ℚ) < 607 * k + 455 := by nlinarith
      field_simp
      ring
  · -- class 303: alpha = 152, g = 76, beta = 76
    have hnform : n = 607 * k + 303 := by omega
    by_cases hk0 : k = 0
    · have h303 : n = 303 := by omega
      rw [h303]
      refine ⟨76, 23029, 530311812, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨152 * k + 76, 152 * (607 * k + 303), 2 * (152 * k + 76) * (607 * k + 303), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 152 * k + 76 := by nlinarith
        have hk2 : (0 : ℚ) < 607 * k + 303 := by nlinarith
        field_simp
        ring
