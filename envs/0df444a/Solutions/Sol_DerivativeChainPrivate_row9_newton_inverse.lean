-- Prove2me | solution 1 for DerivativeChainPrivate.row9_newton_inverse
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T21:04:11.361864+00:00
-- url     : https://prove2.me/submissions/21bff674-bd03-4f24-9f66-b5c6f4ed39d4

import Definitions.Def_DerivativeChainPrivate_fifth_row9_inverse_residual
import Definitions.Def_DerivativeChainPrivate_fifth_row9_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row9_product0
import Definitions.Def_DerivativeChainPrivate_fifth_row9_product1
import Definitions.Def_DerivativeChainPrivate_fifth_row9_product2
import Definitions.Def_DerivativeChainPrivate_fifth_row9_product3
import Definitions.Def_DerivativeChainPrivate_fifth_row9_qp
import Definitions.Def_DerivativeChainPrivate_fifth_row9_square
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_row9_newton_product_0
import Theorems.Thm_DerivativeChainPrivate_row9_newton_product_1
import Theorems.Thm_DerivativeChainPrivate_row9_newton_product_2
import Theorems.Thm_DerivativeChainPrivate_row9_newton_product_3
import Theorems.Thm_DerivativeChainPrivate_row9_newton_qp
import Theorems.Thm_DerivativeChainPrivate_row9_newton_square
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


section
-- Source module: Row9ProductData

set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators












theorem row9_square_split (α : ℝ) (t : ℂ) :
    row9S α t=row9SBlock0 α t+t^16*row9SBlock1 α t+t^32*row9SBlock2 α t+t^48*row9SBlock3 α t := by
  norm_num [row9S,row9SBlock0,row9SBlock1,row9SBlock2,row9SBlock3,Fin.sum_univ_succ,Fin.succ]
  ring <;> rfl
end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution (α : ℝ)
    (hα : α^3=(1001/2)+(-462)*α+(84)*α^2) (t : ℂ) :
    1-row9Q α t*(row9G1 t+2*row9G2 t*row9P α t+3*row9G3 t*(row9P α t)^2) = t^32*row9J α t := by
  have hsquare := row9_newton_square α hα t
  have hQP := row9_newton_qp α hα t
  have hQS : row9Q α t*row9S α t = row9U0 α t+t^16*row9U1 α t+t^32*row9U2 α t+t^48*row9U3 α t := by
    rw [row9_square_split]
    linear_combination row9_newton_product_0 α hα t + t^16*(row9_newton_product_1 α hα t) +
      t^32*(row9_newton_product_2 α hα t) + t^48*(row9_newton_product_3 α hα t)
  calc
    _ = 1-row9Q α t*row9G1 t-2*row9G2 t*row9V α t-
        3*row9G3 t*(row9U0 α t+t^16*row9U1 α t+t^32*row9U2 α t+t^48*row9U3 α t) := by
      rw [hsquare]
      linear_combination (-2*row9G2 t)*hQP+(-3*row9G3 t)*hQS
    _ = _ := by
      norm_num [row9V,row9VCoeffs,row9Q,row9QCoeffs,row9J,row9JCoeffs,
        row9U0,row9U0Coeffs,row9U1,row9U1Coeffs,row9U2,row9U2Coeffs,row9U3,row9U3Coeffs,
        row9G0,row9G1,row9G2,row9G3,Fin.sum_univ_succ]
      push_cast
      ring
