-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BudgetLiftBounds.sqrt_le_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:38.810624+00:00
-- url     : https://prove2.me/submissions/c391f5f1-824f-482f-b93a-8b570a74c2f8

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetLiftSquareRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BudgetLiftBounds
namespace Formalism.FourierDecayAlt.P.BudgetLiftBounds
theorem _root_.solution {x c d L : ℝ} (hx : x ≤ c * L) (hc0 : 0 ≤ c) (hcd : c ≤ d ^ 2) (hd : 0 ≤ d) :
    √x ≤ d * √L := by
  rcases le_or_gt 0 L with hL | hL
  · have : x ≤ d ^ 2 * L := le_trans hx (mul_le_mul_of_nonneg_right hcd hL)
    calc √x ≤ √(d ^ 2 * L) := Real.sqrt_le_sqrt this
      _ = d * √L := by rw [Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd]
  · have : x ≤ 0 := le_trans hx (mul_nonpos_of_nonneg_of_nonpos hc0 hL.le)
    rw [Real.sqrt_eq_zero_of_nonpos this]
    exact mul_nonneg hd (Real.sqrt_nonneg _)
end Formalism.FourierDecayAlt.P.BudgetLiftBounds
