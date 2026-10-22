-- Prove2me | solution 1 for GDGen3.am_sum
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:51:39.196448+00:00
-- url     : https://prove2.me/submissions/d6f085d8-351c-403c-81ab-9fdce1b80d23

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (ξ : ℕ → ℝ) (h0 : ξ 0 = 0) : ∀ i : ℕ,
    Finset.sum (Finset.range (i + 1)) (fun k => Am ξ k)
      = Finset.sum (Finset.range i) (fun k => Abar ξ k) := by
  intro i
  induction i with
  | zero => simp [Am]
  | succ m ih =>
    have hstep : Am ξ (m + 1) = Abar ξ m := by
      rw [Am, if_neg (by omega : ¬ m + 1 = 0), Nat.add_sub_cancel]
    rw [Finset.sum_range_succ, ih, hstep, Finset.sum_range_succ]
