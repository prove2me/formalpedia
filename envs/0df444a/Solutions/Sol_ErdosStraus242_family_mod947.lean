-- Prove2me | solution 1 for ErdosStraus242.family_mod947
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:13:05.246177+00:00
-- url     : https://prove2.me/submissions/cb403ae9-a0ea-480f-82e6-4340fea08452

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 947 ∈ ({943, 935, 631} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 947
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 947 * k + n % 947 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h
  · -- class 943: alpha = 237, g = 1, beta = 236
    have hnform : n = 947 * k + 943 := by omega
    rw [hnform]
    refine ⟨237 * k + 236, 237 * (947 * k + 943), 237 * (237 * k + 236) * (947 * k + 943), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 237 * k + 236 := by nlinarith
      have hk2 : (0 : ℚ) < 947 * k + 943 := by nlinarith
      field_simp
      ring
  · -- class 935: alpha = 237, g = 3, beta = 234
    have hnform : n = 947 * k + 935 := by omega
    rw [hnform]
    refine ⟨237 * k + 234, 237 * (947 * k + 935), 79 * (237 * k + 234) * (947 * k + 935), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 237 * k + 234 := by nlinarith
      have hk2 : (0 : ℚ) < 947 * k + 935 := by nlinarith
      field_simp
      ring
  · -- class 631: alpha = 237, g = 79, beta = 158
    have hnform : n = 947 * k + 631 := by omega
    rw [hnform]
    refine ⟨237 * k + 158, 237 * (947 * k + 631), 3 * (237 * k + 158) * (947 * k + 631), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 237 * k + 158 := by nlinarith
      have hk2 : (0 : ℚ) < 947 * k + 631 := by nlinarith
      field_simp
      ring
