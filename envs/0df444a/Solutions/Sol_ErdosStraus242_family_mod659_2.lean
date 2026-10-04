-- Prove2me | solution 2 for ErdosStraus242.family_mod659
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:21.14578+00:00
-- url     : https://prove2.me/submissions/2b34c4c9-e3c8-4b2f-bdb3-8f64382eb4a6

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 659 ∈ ({655, 647, 639, 615, 599, 527, 439} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 659
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 659 * k + n % 659 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 655: alpha = 165, g = 1, beta = 164
    have hnform : n = 659 * k + 655 := by omega
    rw [hnform]
    refine ⟨165 * k + 164, 165 * (659 * k + 655), 165 * (165 * k + 164) * (659 * k + 655), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 165 * k + 164 := by nlinarith
      have hk2 : (0 : ℚ) < 659 * k + 655 := by nlinarith
      field_simp
      ring
  · -- class 647: alpha = 165, g = 3, beta = 162
    have hnform : n = 659 * k + 647 := by omega
    rw [hnform]
    refine ⟨165 * k + 162, 165 * (659 * k + 647), 55 * (165 * k + 162) * (659 * k + 647), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 165 * k + 162 := by nlinarith
      have hk2 : (0 : ℚ) < 659 * k + 647 := by nlinarith
      field_simp
      ring
  · -- class 639: alpha = 165, g = 5, beta = 160
    have hnform : n = 659 * k + 639 := by omega
    rw [hnform]
    refine ⟨165 * k + 160, 165 * (659 * k + 639), 33 * (165 * k + 160) * (659 * k + 639), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 165 * k + 160 := by nlinarith
      have hk2 : (0 : ℚ) < 659 * k + 639 := by nlinarith
      field_simp
      ring
  · -- class 615: alpha = 165, g = 11, beta = 154
    have hnform : n = 659 * k + 615 := by omega
    rw [hnform]
    refine ⟨165 * k + 154, 165 * (659 * k + 615), 15 * (165 * k + 154) * (659 * k + 615), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 165 * k + 154 := by nlinarith
      have hk2 : (0 : ℚ) < 659 * k + 615 := by nlinarith
      field_simp
      ring
  · -- class 599: alpha = 165, g = 15, beta = 150
    have hnform : n = 659 * k + 599 := by omega
    rw [hnform]
    refine ⟨165 * k + 150, 165 * (659 * k + 599), 11 * (165 * k + 150) * (659 * k + 599), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 165 * k + 150 := by nlinarith
      have hk2 : (0 : ℚ) < 659 * k + 599 := by nlinarith
      field_simp
      ring
  · -- class 527: alpha = 165, g = 33, beta = 132
    have hnform : n = 659 * k + 527 := by omega
    rw [hnform]
    refine ⟨165 * k + 132, 165 * (659 * k + 527), 5 * (165 * k + 132) * (659 * k + 527), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 165 * k + 132 := by nlinarith
      have hk2 : (0 : ℚ) < 659 * k + 527 := by nlinarith
      field_simp
      ring
  · -- class 439: alpha = 165, g = 55, beta = 110
    have hnform : n = 659 * k + 439 := by omega
    rw [hnform]
    refine ⟨165 * k + 110, 165 * (659 * k + 439), 3 * (165 * k + 110) * (659 * k + 439), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 165 * k + 110 := by nlinarith
      have hk2 : (0 : ℚ) < 659 * k + 439 := by nlinarith
      field_simp
      ring
