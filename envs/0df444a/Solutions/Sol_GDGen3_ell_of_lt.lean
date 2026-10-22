-- Prove2me | solution 1 for GDGen3.ell_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:48:46.787846+00:00
-- url     : https://prove2.me/submissions/33cacff6-678d-4006-8a2d-ac7b1f002609

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N : ℕ) {k j : ℕ} (h : k < j) :
    ell r ξ N k j = (Abar ξ k - Am ξ k) * (D r ξ N j + r * D r ξ N (j + 1)) := by
  simp only [ell, if_pos h]
