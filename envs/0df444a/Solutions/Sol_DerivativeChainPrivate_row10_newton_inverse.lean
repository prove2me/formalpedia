-- Prove2me | solution 1 for DerivativeChainPrivate.row10_newton_inverse
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T21:44:54.527767+00:00
-- url     : https://prove2.me/submissions/28213ae6-0e76-4d42-a56f-d2af3c135d16

import Definitions.Def_DerivativeChainPrivate_fifth_row10_inverse_residual
import Definitions.Def_DerivativeChainPrivate_fifth_row10_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row10_product0
import Definitions.Def_DerivativeChainPrivate_fifth_row10_product1
import Definitions.Def_DerivativeChainPrivate_fifth_row10_product2
import Definitions.Def_DerivativeChainPrivate_fifth_row10_product3
import Definitions.Def_DerivativeChainPrivate_fifth_row10_qp
import Definitions.Def_DerivativeChainPrivate_fifth_row10_square
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_row10_newton_product_0
import Theorems.Thm_DerivativeChainPrivate_row10_newton_product_1
import Theorems.Thm_DerivativeChainPrivate_row10_newton_product_2
import Theorems.Thm_DerivativeChainPrivate_row10_newton_product_3
import Theorems.Thm_DerivativeChainPrivate_row10_newton_qp
import Theorems.Thm_DerivativeChainPrivate_row10_newton_square
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


section
-- Source module: Row10ProductData

set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators












theorem row10_square_split (α : ℝ) (t : ℂ) :
    row10S α t=row10SBlock0 α t+t^16*row10SBlock1 α t+t^32*row10SBlock2 α t+t^48*row10SBlock3 α t := by
  norm_num [row10S,row10SBlock0,row10SBlock1,row10SBlock2,row10SBlock3,Fin.sum_univ_succ,Fin.succ]
  ring <;> rfl
end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution (α : ℝ)
    (hα : α^3=(1001/20)+(-66)*α+(21)*α^2) (t : ℂ) :
    1-row10Q α t*(row10G1 t+2*row10G2 t*row10P α t+3*row10G3 t*(row10P α t)^2) = t^32*row10J α t := by
  have hsquare := row10_newton_square α hα t
  have hQP := row10_newton_qp α hα t
  have hQS : row10Q α t*row10S α t = row10U0 α t+t^16*row10U1 α t+t^32*row10U2 α t+t^48*row10U3 α t := by
    rw [row10_square_split]
    linear_combination row10_newton_product_0 α hα t + t^16*(row10_newton_product_1 α hα t) +
      t^32*(row10_newton_product_2 α hα t) + t^48*(row10_newton_product_3 α hα t)
  calc
    _ = 1-row10Q α t*row10G1 t-2*row10G2 t*row10V α t-
        3*row10G3 t*(row10U0 α t+t^16*row10U1 α t+t^32*row10U2 α t+t^48*row10U3 α t) := by
      rw [hsquare]
      linear_combination (-2*row10G2 t)*hQP+(-3*row10G3 t)*hQS
    _ = _ := by
      norm_num [row10V,row10VCoeffs,row10Q,row10QCoeffs,row10J,row10JCoeffs,
        row10U0,row10U0Coeffs,row10U1,row10U1Coeffs,row10U2,row10U2Coeffs,row10U3,row10U3Coeffs,
        row10G0,row10G1,row10G2,row10G3,Fin.sum_univ_succ]
      push_cast
      ring
