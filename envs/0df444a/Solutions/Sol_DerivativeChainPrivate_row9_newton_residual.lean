-- Prove2me | solution 1 for DerivativeChainPrivate.row9_newton_residual
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T19:46:17.068435+00:00
-- url     : https://prove2.me/submissions/af5c093c-df0b-4847-9218-f010c6215007

import Definitions.Def_DerivativeChainPrivate_fifth_row9_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row9_residual
import Definitions.Def_DerivativeChainPrivate_fifth_row9_square
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_row9_newton_square
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open DerivativeChainPrivate in
theorem solution (α : ℝ)
    (hα : α^3=(1001/2)+(-462)*α+(84)*α^2) (t : ℂ) :
    row9G0 t+row9G1 t*row9P α t+row9G2 t*(row9P α t)^2+row9G3 t*(row9P α t)^3 = t^32*row9E α t := by
  have h3 : (α:ℂ)^3 = (1001/2:ℂ)+(-462)*(α:ℂ)+(84)*(α:ℂ)^2 := by
    have hh := congrArg (fun x : ℝ => (x:ℂ)) hα
    push_cast at hh
    norm_num at hh ⊢
    exact hh
  have h4 : (α:ℂ)^4 = (42042:ℂ)+(-76615/2)*(α:ℂ)+(6594)*(α:ℂ)^2 := by
    have hh : (α:ℂ)^4 = (α:ℂ)*((1001/2:ℂ)+(-462)*(α:ℂ)+(84)*(α:ℂ)^2) := by
      linear_combination (α:ℂ)*h3
    calc
      _ = (α:ℂ)*((1001/2:ℂ)+(-462)*(α:ℂ)+(84)*(α:ℂ)^2) := hh
      _ = (1001/2:ℂ)*(α:ℂ)+(-462)*(α:ℂ)^2+(84)*(α:ℂ)^3 := by ring
      _ = _ := by rw [h3]; ring
  have hsquare := row9_newton_square α hα t
  simp only [show (row9P α t)^3=(row9P α t)^2*(row9P α t) by ring,hsquare]
  norm_num [row9S,row9SCoeffs,row9P,row9PCoeffs,row9E,row9ECoeffs,row9G0,row9G1,row9G2,row9G3,Fin.sum_univ_succ]
  push_cast
  ring_nf
  simp only [h3,h4]
  ring
