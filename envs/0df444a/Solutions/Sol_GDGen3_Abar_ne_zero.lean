-- Prove2me | solution 1 for GDGen3.Abar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:41:00.638774+00:00
-- url     : https://prove2.me/submissions/2c57bc89-7383-4bd6-80b9-d5d2f7c35409

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (ξ : ℕ → ℝ) (h0 : ξ 0 = 0) (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) :
    ∀ i : ℕ, Abar ξ i ≠ 0 := by
  intro i
  induction i with
  | zero => simp [Abar]
  | succ k ih =>
    have h1 : 1 + ξ k ≠ 0 := by
      by_cases hk : k = 0
      · simp [hk, h0]
      · have := hpos k hk; linarith
    rw [Abar]
    exact div_ne_zero (mul_ne_zero ih h1) (ne_of_gt (hpos (k + 1) (by omega)))
