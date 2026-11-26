-- Prove2me | solution 1 for ContinuousLinearMap.adjoint_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:03.288748+00:00
-- url     : https://prove2.me/submissions/1a2c547c-92c3-47ff-876a-9f401efab617

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Definitions.Def_Operator_Crouzeix_AdjointIntegral

set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace Interval
universe u v w
open ContinuousLinearMap
variable {X : Type u} [MeasurableSpace X] {μ : Measure X}
variable {E : Type v} {F : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace ContinuousLinearMap
theorem _root_.solution (f : X → E →L[ℂ] F) (hf : Integrable f μ) :
    ContinuousLinearMap.adjoint (∫ x, f x ∂μ) =
      ∫ x, ContinuousLinearMap.adjoint (f x) ∂μ := by
  symm
  exact ContinuousLinearMap.integral_comp_commSL
    RCLike.conj_smul
    ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap hf
end ContinuousLinearMap
