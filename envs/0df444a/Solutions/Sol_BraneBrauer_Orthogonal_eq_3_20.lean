-- Prove2me | solution 1 for BraneBrauer.Orthogonal.eq_3_20
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T20:59:43.436987+00:00
-- url     : https://prove2.me/submissions/33bd596a-5a17-451f-8971-5d3b42975a13

import Mathlib
import Definitions.Def_BraneBrauer_Orthogonal_Setting

noncomputable section
open BraneBrauer.Orthogonal

theorem solution {N m n : ℕ} (X Y : Op N m n) :
    (X * Y).trace = (sigma X * sigma Y).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, sigma, Matrix.of_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  symm
  exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm))
