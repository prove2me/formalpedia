-- Prove2me | solution 2 for GDGen3.am_telescope2
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:29:15.392653+00:00
-- url     : https://prove2.me/submissions/59798705-ed37-42f6-9a91-47818acc2b9a

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_am_sum

noncomputable section

open Finset

open GDGen3

theorem solution (ξ : ℕ → ℝ) (h0 : ξ 0 = 0) (r : ℝ) (i : ℕ) :
    Finset.sum (Finset.range (i + 1)) (fun k => Am ξ k + r * Abar ξ k)
      = (Finset.sum (Finset.range i) (fun k => Abar ξ k))
        + r * (Abar ξ i + Finset.sum (Finset.range i) (fun k => Abar ξ k)) := by
  have hsplit : Finset.sum (Finset.range (i + 1)) (fun k => Am ξ k + r * Abar ξ k)
      = Finset.sum (Finset.range (i + 1)) (fun k => Am ξ k)
        + r * Finset.sum (Finset.range (i + 1)) (fun k => Abar ξ k) := by
    rw [Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsplit, am_sum ξ h0 i, Finset.sum_range_succ]
  ring
