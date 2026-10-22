-- Prove2me | solution 2 for GDGen3.ell_pair_sum
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:29:19.679975+00:00
-- url     : https://prove2.me/submissions/e0866cad-cb91-4397-9f4c-c8b13a740aec

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_ell_of_lt
import Theorems.Thm_GDGen3_ell_of_gt

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N a b : ℕ) (hab : a < b) :
    ell r ξ N a b + ell r ξ N b a =
      (1 + r) * (Abar ξ a * D r ξ N b - Am ξ a * D r ξ N (b + 1)) := by
  rw [ell_of_lt r ξ N hab, ell_of_gt r ξ N hab]
  ring
