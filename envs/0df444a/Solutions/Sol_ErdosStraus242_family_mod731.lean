-- Prove2me | solution 1 for ErdosStraus242.family_mod731
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:26.065982+00:00
-- url     : https://prove2.me/submissions/847f1503-9270-496e-b09c-94d75037dd81

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 731 ∈ ({727, 719, 487} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 731
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 731 * k + n % 731 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 727: alpha = 183, g = 1, beta = 182
    have hnform : n = 731 * k + 727 := by omega
    rw [hnform]
    refine ⟨183 * k + 182, 183 * (731 * k + 727), 183 * (183 * k + 182) * (731 * k + 727), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 183 * k + 182 := by nlinarith
      have hk2 : (0 : ℚ) < 731 * k + 727 := by nlinarith
      field_simp
      ring
  · -- class 719: alpha = 183, g = 3, beta = 180
    have hnform : n = 731 * k + 719 := by omega
    rw [hnform]
    refine ⟨183 * k + 180, 183 * (731 * k + 719), 61 * (183 * k + 180) * (731 * k + 719), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 183 * k + 180 := by nlinarith
      have hk2 : (0 : ℚ) < 731 * k + 719 := by nlinarith
      field_simp
      ring
  · -- class 487: alpha = 183, g = 61, beta = 122
    have hnform : n = 731 * k + 487 := by omega
    rw [hnform]
    refine ⟨183 * k + 122, 183 * (731 * k + 487), 3 * (183 * k + 122) * (731 * k + 487), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 183 * k + 122 := by nlinarith
      have hk2 : (0 : ℚ) < 731 * k + 487 := by nlinarith
      field_simp
      ring
