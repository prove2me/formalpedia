-- Prove2me | solution 1 for GDGen3.flow_total
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:10:02.935437+00:00
-- url     : https://prove2.me/submissions/b2ed7365-ea0c-419c-b805-dbed812e2a59

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_sum_antisymm

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range (N + 1), d r ξ N i) = 0 := by
  exact sum_antisymm (ell r ξ N) (range (N + 1))
