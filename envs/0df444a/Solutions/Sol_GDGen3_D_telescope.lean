-- Prove2me | solution 1 for GDGen3.D_telescope
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:52:38.266555+00:00
-- url     : https://prove2.me/submissions/f08cd2c8-07b8-4a6e-acdb-6e59286b3898

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) (hi : i + 1 ≤ N) :
    Finset.sum (Finset.Icc (i + 1) N) (fun j => D r ξ N j - D r ξ N (j + 1)) = D r ξ N (i + 1) := by
  have hDN : D r ξ N (N + 1) = 0 := by
    rw [D, if_pos (Or.inr (by omega : N < N + 1))]
  have key : ∀ M, i + 1 ≤ M → M ≤ N →
      Finset.sum (Finset.Icc (i + 1) M) (fun j => D r ξ N j - D r ξ N (j + 1))
        = D r ξ N (i + 1) - D r ξ N (M + 1) := by
    intro M h1 _
    induction M, h1 using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
      rw [Finset.sum_Icc_succ_top (a := i + 1) (b := b) (by omega), ih (by omega)]
      ring
  rw [key N hi le_rfl, hDN, sub_zero]
