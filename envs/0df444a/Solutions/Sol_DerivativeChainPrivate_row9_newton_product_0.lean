-- Prove2me | solution 1 for DerivativeChainPrivate.row9_newton_product_0
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T20:52:57.658598+00:00
-- url     : https://prove2.me/submissions/e3a90e70-31c6-4121-bac1-bff92587f7d6

import Definitions.Def_DerivativeChainPrivate_fifth_row9_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row9_product0
import Definitions.Def_DerivativeChainPrivate_fifth_row9_square
import Mathlib
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open DerivativeChainPrivate in
theorem solution (α : ℝ)
    (hα : α^3=(1001/2)+(-462)*α+(84)*α^2) (t : ℂ) :
    row9Q α t*row9SBlock0 α t=row9U0 α t := by
  have h3 : (α:ℂ)^3=(1001/2:ℂ)+(-462)*(α:ℂ)+(84)*(α:ℂ)^2 := by
    have hh := congrArg (fun x : ℝ => (x:ℂ)) hα
    push_cast at hh
    norm_num at hh ⊢
    exact hh
  have h4 : (α:ℂ)^4=(42042:ℂ)+(-76615/2)*(α:ℂ)+(6594)*(α:ℂ)^2 := by
    have hh : (α:ℂ)^4=(α:ℂ)*((1001/2:ℂ)+(-462)*(α:ℂ)+(84)*(α:ℂ)^2) := by linear_combination (α:ℂ)*h3
    calc
      _ = (α:ℂ)*((1001/2:ℂ)+(-462)*(α:ℂ)+(84)*(α:ℂ)^2) := hh
      _ = (1001/2:ℂ)*(α:ℂ)+(-462)*(α:ℂ)^2+(84)*(α:ℂ)^3 := by ring
      _ = _ := by rw [h3]; ring
  norm_num [row9Q,row9QCoeffs,row9SBlock0,row9SCoeffs,row9U0,row9U0Coeffs,Fin.sum_univ_succ]
  push_cast
  ring_nf
  simp only [h3,h4]
  ring
