-- Prove2me | solution 1 for DerivativeChainPrivate.row10_newton_residual
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T21:16:54.127684+00:00
-- url     : https://prove2.me/submissions/8727bc8b-fb18-4444-ae71-40f85469a03f

import Definitions.Def_DerivativeChainPrivate_fifth_row10_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row10_residual
import Definitions.Def_DerivativeChainPrivate_fifth_row10_square
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_row10_newton_square
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open DerivativeChainPrivate in
theorem solution (α : ℝ)
    (hα : α^3=(1001/20)+(-66)*α+(21)*α^2) (t : ℂ) :
    row10G0 t+row10G1 t*row10P α t+row10G2 t*(row10P α t)^2+row10G3 t*(row10P α t)^3 = t^32*row10E α t := by
  have h3 : (α:ℂ)^3 = (1001/20:ℂ)+(-66)*(α:ℂ)+(21)*(α:ℂ)^2 := by
    have hh := congrArg (fun x : ℝ => (x:ℂ)) hα
    push_cast at hh
    norm_num at hh ⊢
    exact hh
  have h4 : (α:ℂ)^4 = (21021/20:ℂ)+(-26719/20)*(α:ℂ)+(375)*(α:ℂ)^2 := by
    have hh : (α:ℂ)^4 = (α:ℂ)*((1001/20:ℂ)+(-66)*(α:ℂ)+(21)*(α:ℂ)^2) := by
      linear_combination (α:ℂ)*h3
    calc
      _ = (α:ℂ)*((1001/20:ℂ)+(-66)*(α:ℂ)+(21)*(α:ℂ)^2) := hh
      _ = (1001/20:ℂ)*(α:ℂ)+(-66)*(α:ℂ)^2+(21)*(α:ℂ)^3 := by ring
      _ = _ := by rw [h3]; ring
  have hsquare := row10_newton_square α hα t
  simp only [show (row10P α t)^3=(row10P α t)^2*(row10P α t) by ring,hsquare]
  norm_num [row10S,row10SCoeffs,row10P,row10PCoeffs,row10E,row10ECoeffs,row10G0,row10G1,row10G2,row10G3,Fin.sum_univ_succ]
  push_cast
  ring_nf
  simp only [h3,h4]
  ring
