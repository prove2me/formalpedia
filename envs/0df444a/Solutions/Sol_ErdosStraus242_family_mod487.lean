-- Prove2me | solution 1 for ErdosStraus242.family_mod487
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:06:34.080258+00:00
-- url     : https://prove2.me/submissions/22cd26c1-7822-408e-89e7-9d7855ef70a9

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 487 ∈ ({483, 479, 243} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 487
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 487 * k + n % 487 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 483: alpha = 122, g = 1, beta = 121
    have hnform : n = 487 * k + 483 := by omega
    rw [hnform]
    refine ⟨122 * k + 121, 122 * (487 * k + 483), 122 * (122 * k + 121) * (487 * k + 483), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 122 * k + 121 := by nlinarith
      have hk2 : (0 : ℚ) < 487 * k + 483 := by nlinarith
      field_simp
      ring
  · -- class 479: alpha = 122, g = 2, beta = 120
    have hnform : n = 487 * k + 479 := by omega
    rw [hnform]
    refine ⟨122 * k + 120, 122 * (487 * k + 479), 61 * (122 * k + 120) * (487 * k + 479), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 122 * k + 120 := by nlinarith
      have hk2 : (0 : ℚ) < 487 * k + 479 := by nlinarith
      field_simp
      ring
  · -- class 243: alpha = 122, g = 61, beta = 61
    have hnform : n = 487 * k + 243 := by omega
    by_cases hk0 : k = 0
    · have h243 : n = 243 := by omega
      rw [h243]
      refine ⟨61, 14824, 219736152, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨122 * k + 61, 122 * (487 * k + 243), 2 * (122 * k + 61) * (487 * k + 243), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 122 * k + 61 := by nlinarith
        have hk2 : (0 : ℚ) < 487 * k + 243 := by nlinarith
        field_simp
        ring
