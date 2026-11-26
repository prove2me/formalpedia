-- Prove2me | solution 1 for ContinuousLinearMap.adjoint_contourIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:06.013678+00:00
-- url     : https://prove2.me/submissions/c7c84d18-7e37-4a2b-a389-eaf65ef39358

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Definitions.Def_Operator_Crouzeix_AdjointIntegral
import Theorems.Thm_ContinuousLinearMap_adjoint_intervalIntegral

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
theorem _root_.solution (f : ℂ → E →L[ℂ] F) (γ : ℝ → ℂ)
    (hf : ContourIntegrable f γ) :
    ContinuousLinearMap.adjoint (contourIntegral f γ) =
      ∫ t in (0 : ℝ)..(2 * Real.pi),
        star (deriv γ t) • ContinuousLinearMap.adjoint (f (γ t)) := by
  unfold contourIntegral
  rw [adjoint_intervalIntegral _ hf]
  congr 1
  funext t
  exact map_smulₛₗ ContinuousLinearMap.adjoint (deriv γ t) (f (γ t))
end ContinuousLinearMap
