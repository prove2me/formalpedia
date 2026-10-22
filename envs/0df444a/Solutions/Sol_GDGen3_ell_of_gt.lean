-- Prove2me | solution 1 for GDGen3.ell_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:49:45.685984+00:00
-- url     : https://prove2.me/submissions/95866608-4201-432c-8d76-899d0d747eb4

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N : ℕ) {k j : ℕ} (h : j < k) :
    ell r ξ N k j = (Am ξ j + r * Abar ξ j) * (D r ξ N k - D r ξ N (k + 1)) := by
  rw [ell, if_neg (Nat.not_lt.mpr (le_of_lt h))]
