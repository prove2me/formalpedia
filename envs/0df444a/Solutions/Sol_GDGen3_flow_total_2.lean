-- Prove2me | solution 2 for GDGen3.flow_total
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:31:13.654995+00:00
-- url     : https://prove2.me/submissions/96b8d27d-07f6-4abf-8838-10d465b53a1a

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_sum_antisymm

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range (N + 1), d r ξ N i) = 0 := by
  exact sum_antisymm (ell r ξ N) (range (N + 1))
