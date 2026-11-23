-- Prove2me | solution 1 for Formalism.DivisionValues.operator_norm_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:23.130576+00:00
-- url     : https://prove2.me/submissions/cc1b86e0-6e48-46c6-82f7-f81875a86e06

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_opNorm_le_iff
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_pairC_eq
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_dot_frames
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_opNormAt_dual_eq
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_mul_inv_mulVec
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_inv_mul_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open OperatorNormFrames
namespace Formalism.DivisionValues
theorem _root_.solution : OpNormDual := by
  unfold OpNormDual
  intro K _ _ _ a D XM XE hM hE B v c hc
  rw [opNormAt_dual_eq XM XE hE B v, opNorm_le_iff _ c hc]
  constructor
  · intro h x y
    have h1 := h ((XM v)⁻¹.mulVec x) ((XE v)⁻¹.mulVec y)
    rw [dot_frames, mul_inv_mulVec _ (hE v), mul_inv_mulVec _ (hM v)] at h1
    rw [pairC_eq]
    exact h1
  · intro h x y
    have h1 := h ((XM v).mulVec x) ((XE v).mulVec y)
    rw [pairC_eq] at h1
    rw [dot_frames]
    simpa only [fnorm, inv_mul_mulVec _ (hM v), inv_mul_mulVec _ (hE v)] using h1
end Formalism.DivisionValues
