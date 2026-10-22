-- Prove2me | solution 2 for GDGen3.mixed_coeff_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:35:33.894979+00:00
-- url     : https://prove2.me/submissions/ac7fe96e-2dc1-4ab4-8695-ccae9dad457c

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_ell_pair_sum
import Theorems.Thm_GDGen3_incoming_prefix
import Theorems.Thm_GDGen3_incoming_suffix

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N a b : ℕ)
    (hab : a < b) (hb : b ≤ N) :
    ell r ξ N a b + ell r ξ N b a =
      (1 + r) * ((∑ i ∈ range (a + 1), ell r ξ N i b)
        - ∑ i ∈ Icc (b + 1) N, ell r ξ N i a) := by
  rw [ell_pair_sum r ξ N a b hab, incoming_prefix r ξ N a b hab,
    incoming_suffix r ξ N a b (le_of_lt hab) hb]
  ring
