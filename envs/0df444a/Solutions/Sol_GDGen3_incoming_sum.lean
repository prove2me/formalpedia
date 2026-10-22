-- Prove2me | solution 1 for GDGen3.incoming_sum
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:09:18.776794+00:00
-- url     : https://prove2.me/submissions/70e22ce5-dad2-43e0-af28-50c4d06913a2

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_sum_suffix_indicator
import Theorems.Thm_GDGen3_total_sub_suffix

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) (hi : i ≤ N) :
    (∑ j ∈ range (N + 1), ell r ξ N j i) = U r ξ N i + ell r ξ N i i + V r ξ N i := by
  have h := total_sub_suffix (fun j => ell r ξ N j i) N i hi
  have hp : (∑ j ∈ range (i + 1), ell r ξ N j i) =
      (∑ j ∈ range i, ell r ξ N j i) + ell r ξ N i i := sum_range_succ _ i
  rw [hp, sum_suffix_indicator] at h
  unfold U V
  linarith
