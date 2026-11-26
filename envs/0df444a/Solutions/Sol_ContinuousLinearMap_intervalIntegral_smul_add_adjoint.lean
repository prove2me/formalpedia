-- Prove2me | solution 1 for ContinuousLinearMap.intervalIntegral_smul_add_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:16.269408+00:00
-- url     : https://prove2.me/submissions/523bdc27-7022-4e82-b63a-f5e2fc8919ab

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
theorem _root_.solution (K : ℝ → E →L[ℂ] E) (f : ℝ → ℂ)
    {a b : ℝ} {ν : Measure ℝ}
    (hfK : IntervalIntegrable (fun t => f t • K t) ν a b)
    (hstarfK : IntervalIntegrable (fun t => star (f t) • K t) ν a b) :
    (∫ t in a..b, f t • K t ∂ν) +
        ContinuousLinearMap.adjoint (∫ t in a..b, star (f t) • K t ∂ν) =
      ∫ t in a..b,
        f t • (K t + ContinuousLinearMap.adjoint (K t)) ∂ν := by
  let adjointCLM : (E →L[ℂ] E) →L⋆[ℂ] (E →L[ℂ] E) :=
    ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap
  have hfAdjointK : IntervalIntegrable
      (fun t => f t • ContinuousLinearMap.adjoint (K t)) ν a b := by
    have hcomp : IntervalIntegrable
        (fun t => adjointCLM (star (f t) • K t)) ν a b :=
      ⟨adjointCLM.integrable_comp hstarfK.1,
        adjointCLM.integrable_comp hstarfK.2⟩
    have hfun : (fun t => adjointCLM (star (f t) • K t)) =
        fun t => f t • ContinuousLinearMap.adjoint (K t) := by
      funext t
      change ContinuousLinearMap.adjoint (star (f t) • K t) =
        f t • ContinuousLinearMap.adjoint (K t)
      exact (map_smulₛₗ ContinuousLinearMap.adjoint (star (f t)) (K t)).trans (by
        rw [starRingEnd_apply, star_star])
    rw [hfun] at hcomp
    exact hcomp
  rw [adjoint_intervalIntegral _ hstarfK]
  have hadjoint : (fun t => ContinuousLinearMap.adjoint (star (f t) • K t)) =
      fun t => f t • ContinuousLinearMap.adjoint (K t) := by
    funext t
    exact (map_smulₛₗ ContinuousLinearMap.adjoint (star (f t)) (K t)).trans (by
      rw [starRingEnd_apply, star_star])
  rw [hadjoint, ← intervalIntegral.integral_add hfK hfAdjointK]
  congr 1
  funext t
  exact (smul_add (f t) (K t) (ContinuousLinearMap.adjoint (K t))).symm
end ContinuousLinearMap
