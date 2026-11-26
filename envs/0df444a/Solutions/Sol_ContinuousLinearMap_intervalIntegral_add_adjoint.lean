-- Prove2me | solution 1 for ContinuousLinearMap.intervalIntegral_add_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:20.836012+00:00
-- url     : https://prove2.me/submissions/ba8d3ce4-3db0-4247-a039-fee5c071c0f8

import Definitions.Def_Operator_Crouzeix_AdjointIntegral
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Theorems.Thm_ContinuousLinearMap_adjoint_intervalIntegral


set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
open ContinuousLinearMap
namespace ContinuousLinearMap
theorem _root_.solution {f : ℝ → E →L[ℂ] E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, f t + ContinuousLinearMap.adjoint (f t)) =
      (∫ t in a..b, f t) +
        ContinuousLinearMap.adjoint (∫ t in a..b, f t) := by
  let adj : (E →L[ℂ] E) →L⋆[ℂ] (E →L[ℂ] E) :=
    ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap
  have hfadj : IntervalIntegrable (fun t ↦ ContinuousLinearMap.adjoint (f t))
      volume a b := by
    constructor
    · change Integrable (fun t ↦ adj (f t)) (volume.restrict (Ioc a b))
      exact adj.integrable_comp hf.1
    · change Integrable (fun t ↦ adj (f t)) (volume.restrict (Ioc b a))
      exact adj.integrable_comp hf.2
  rw [intervalIntegral.integral_add hf hfadj,
    ← ContinuousLinearMap.adjoint_intervalIntegral f hf]
end ContinuousLinearMap
