-- Prove2me | solution 1 for GDGen3.mixed_coeff_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:07:53.521806+00:00
-- url     : https://prove2.me/submissions/a8980e12-e641-4a8c-89a2-efdf4d6f03e9

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
