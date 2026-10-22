-- Prove2me | solution 2 for GDGen3.incoming_sum
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:32:22.699171+00:00
-- url     : https://prove2.me/submissions/ecdc2478-0520-4805-ab3f-9475b0b02d63

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
