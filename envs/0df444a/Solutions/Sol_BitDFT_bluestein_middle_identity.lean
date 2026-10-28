-- Prove2me | solution 1 for BitDFT.bluestein_middle_identity
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-25T04:43:13.132485+00:00
-- url     : https://prove2.me/submissions/ba076b88-318b-48e0-ba88-f22d6f1a99b4

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem solution {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0)
    (X : Fin n → ℂ) (k : Fin n) :
    ρ ^ ((k.val : ℤ) ^ 2) *
        (∑ j : Fin n, X j * ρ ^ ((j.val : ℤ) ^ 2) *
          ρ ^ (-((k.val : ℤ) - (j.val : ℤ)) ^ 2)) =
      ∑ j : Fin n, X j * (ρ ^ 2) ^ (j.val * k.val) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  calc
    ρ ^ ((k.val : ℤ) ^ 2) *
        (X j * ρ ^ ((j.val : ℤ) ^ 2) * ρ ^ (-((k.val : ℤ) - (j.val : ℤ)) ^ 2)) =
      X j * (ρ ^ ((k.val : ℤ) ^ 2) * ρ ^ ((j.val : ℤ) ^ 2) *
        ρ ^ (-((k.val : ℤ) - (j.val : ℤ)) ^ 2)) := by ring
    _ = X j * ρ ^ (((k.val : ℤ) ^ 2 + (j.val : ℤ) ^ 2) +
        (-((k.val : ℤ) - (j.val : ℤ)) ^ 2)) := by
      rw [← zpow_add₀ hρ, ← zpow_add₀ hρ]
    _ = X j * ρ ^ (2 * ((j.val * k.val : ℕ) : ℤ)) := by
      congr 2
      push_cast
      ring
    _ = X j * (ρ ^ 2) ^ (j.val * k.val) := by
      rw [zpow_mul]
      simp only [zpow_natCast, zpow_ofNat]

#print axioms solution
