-- Prove2me | solution 1 for GDGen3.symmetric_square_telescope
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:16:16.953115+00:00
-- url     : https://prove2.me/submissions/98b510bc-88fd-48a4-b113-21d68240bb59

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) (N : ℕ) :
    2 * (∑ i ∈ range N, ∑ j ∈ range i, P i j) + (∑ i ∈ range N, P i i) =
      ∑ i ∈ range N, ∑ j ∈ range N, P i j := by
  induction N with
  | zero => simp
  | succ n ih =>
    simp only [sum_range_succ, sum_add_distrib]
    have he : (∑ i ∈ range n, P i n) = ∑ i ∈ range n, P n i := by
      apply sum_congr rfl; intro i hi; exact hP i n
    rw [he]
    linear_combination ih
