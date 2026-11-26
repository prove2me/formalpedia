-- Prove2me | solution 1 for ContinuousLinearMap.adjoint_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:40.484081+00:00
-- url     : https://prove2.me/submissions/a55750c3-8161-4d68-a278-6f3734338d20

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Definitions.Def_Operator_Crouzeix_AdjointIntegral
import Theorems.Thm_ContinuousLinearMap_adjoint_integral

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
theorem _root_.solution (f : ℝ → E →L[ℂ] F) {a b : ℝ}
    {ν : Measure ℝ} (hf : IntervalIntegrable f ν a b) :
    ContinuousLinearMap.adjoint (∫ x in a..b, f x ∂ν) =
      ∫ x in a..b, ContinuousLinearMap.adjoint (f x) ∂ν := by
  unfold intervalIntegral
  rw [map_sub, adjoint_integral _ hf.1, adjoint_integral _ hf.2]
end ContinuousLinearMap
