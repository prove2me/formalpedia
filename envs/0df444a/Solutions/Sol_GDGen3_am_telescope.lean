-- Prove2me | solution 1 for GDGen3.am_telescope
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:51:53.545773+00:00
-- url     : https://prove2.me/submissions/30ae2f11-22bc-43aa-a762-94d087056d1a

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (ξ : ℕ → ℝ) : ∀ i : ℕ,
    Finset.sum (Finset.range (i + 1)) (fun k => Abar ξ k - Am ξ k) = Abar ξ i := by
  intro i
  induction i with
  | zero => simp [Am, Abar]
  | succ m ih =>
    have hstep : Am ξ (m + 1) = Abar ξ m := by
      rw [Am, if_neg (by omega : ¬ m + 1 = 0), Nat.add_sub_cancel]
    rw [Finset.sum_range_succ, ih, hstep]
    ring
