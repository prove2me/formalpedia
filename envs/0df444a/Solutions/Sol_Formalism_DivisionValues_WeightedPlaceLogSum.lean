-- Prove2me | solution 1 for Formalism.DivisionValues.WeightedPlaceLogSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:51:58.794865+00:00
-- url     : https://prove2.me/submissions/933bec65-63c5-424f-becd-581bc2f387bd

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundRows
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_WeightedPlaceLogSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : LPrimeBound := by
  intro x L b a rd La g nV L' Cg Cn hx hL hb ha hrd hLa hg hlg hnV hlnV hCg hCn hL'
  have hx0 : 0 < x := by linarith
  have hrd0 : 0 < rd := by linarith
  have hb0 : 0 < b := by rw [hb]; exact Real.exp_pos L
  have hlb : Real.log b = L := by rw [hb, Real.log_exp]
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlrd : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have e1 : La = Real.log x + L + Real.log rd := by
    rw [hLa, ha, Real.log_mul (mul_pos hx0 hb0).ne' hrd0.ne', Real.log_mul hx0.ne' hb0.ne', hlb]
  have e2 : L' = L + Real.log rd + Real.log g + Real.log nV := by
    rw [hL', Real.log_mul (mul_pos (mul_pos hb0 hrd0) hg).ne' hnV.ne',
      Real.log_mul (mul_pos hb0 hrd0).ne' hg.ne', Real.log_mul hb0.ne' hrd0.ne', hlb]
  refine ⟨?_, by linarith⟩
  rw [e1, e2]
  nlinarith [mul_nonneg hCg hlx, mul_nonneg hCg hlrd, mul_nonneg hCn hL, mul_nonneg hCn hlrd]
end Formalism.DivisionValues
