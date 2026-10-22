-- Prove2me | solution 2 for GDGen3.diagonal_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:33:58.546369+00:00
-- url     : https://prove2.me/submissions/a213d3d2-ec13-4684-a68b-08a587b5ab2b

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_incoming_sum

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) (hi : i ≤ N) :
    2 * (1 + r) * V r ξ N i - (∑ j ∈ range (N + 1), (ell r ξ N i j + ell r ξ N j i))
      + 2 * ell r ξ N i i = 2 * (r * V r ξ N i - U r ξ N i) - d r ξ N i := by
  have h := incoming_sum r ξ N i hi
  simp only [d, sum_sub_distrib, sum_add_distrib]
  linear_combination -2 * h
