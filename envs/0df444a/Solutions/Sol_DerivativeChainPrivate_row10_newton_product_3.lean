-- Prove2me | solution 1 for DerivativeChainPrivate.row10_newton_product_3
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T21:38:32.58075+00:00
-- url     : https://prove2.me/submissions/4ae4eaa3-94c1-45de-bc24-3ba6eadd3382

import Definitions.Def_DerivativeChainPrivate_fifth_row10_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row10_product3
import Definitions.Def_DerivativeChainPrivate_fifth_row10_square
import Mathlib
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open DerivativeChainPrivate in
theorem solution (α : ℝ)
    (hα : α^3=(1001/20)+(-66)*α+(21)*α^2) (t : ℂ) :
    row10Q α t*row10SBlock3 α t=row10U3 α t := by
  have h3 : (α:ℂ)^3=(1001/20:ℂ)+(-66)*(α:ℂ)+(21)*(α:ℂ)^2 := by
    have hh := congrArg (fun x : ℝ => (x:ℂ)) hα
    push_cast at hh
    norm_num at hh ⊢
    exact hh
  have h4 : (α:ℂ)^4=(21021/20:ℂ)+(-26719/20)*(α:ℂ)+(375)*(α:ℂ)^2 := by
    have hh : (α:ℂ)^4=(α:ℂ)*((1001/20:ℂ)+(-66)*(α:ℂ)+(21)*(α:ℂ)^2) := by linear_combination (α:ℂ)*h3
    calc
      _ = (α:ℂ)*((1001/20:ℂ)+(-66)*(α:ℂ)+(21)*(α:ℂ)^2) := hh
      _ = (1001/20:ℂ)*(α:ℂ)+(-66)*(α:ℂ)^2+(21)*(α:ℂ)^3 := by ring
      _ = _ := by rw [h3]; ring
  norm_num [row10Q,row10QCoeffs,row10SBlock3,row10SCoeffs,row10U3,row10U3Coeffs,Fin.sum_univ_succ]
  push_cast
  ring_nf
  simp only [h3,h4]
  ring
