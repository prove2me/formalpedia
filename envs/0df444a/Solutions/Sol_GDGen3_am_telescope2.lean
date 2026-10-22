-- Prove2me | solution 1 for GDGen3.am_telescope2
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:53:34.881857+00:00
-- url     : https://prove2.me/submissions/d5e17ebb-09ab-409e-bdb0-5633a6c0d393

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
