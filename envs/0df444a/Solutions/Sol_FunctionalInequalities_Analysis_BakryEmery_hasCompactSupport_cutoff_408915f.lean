-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_cutoff_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:44:20.135824+00:00
-- url     : https://prove2.me/submissions/73798201-0b66-4c0c-a573-c433526e7121

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
theorem solution {R : ℝ} (hR : 0 < R) : HasCompactSupport (FunctionalInequalities.Analysis.BakryEmery.cutoff (E := E) R) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * R)) ?_
    intro x hx
    have hxnorm : 2 * R < ‖x‖ := by
      have hnot : ¬‖x‖ ≤ 2 * R := by
        intro h
        apply hx
        simpa [Metric.closedBall, dist_zero_right] using h
      exact lt_of_not_ge hnot
    have hscale : ‖R⁻¹ • x‖ = R⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    have hmul : R⁻¹ * (2 * R) < R⁻¹ * ‖x‖ :=
      mul_lt_mul_of_pos_left hxnorm (inv_pos.mpr hR)
    have heq : R⁻¹ * (2 * R) = 2 := by
      calc
        R⁻¹ * (2 * R) = 2 * (R⁻¹ * R) := by ring
        _ = 2 := by rw [inv_mul_cancel₀ hR.ne', mul_one]
    have hnotball : R⁻¹ • x ∉ Metric.ball (0 : E) 2 := by
      intro h
      have hlt : ‖R⁻¹ • x‖ < 2 := by
        simpa [Metric.ball, dist_zero_right] using h
      rw [hscale, ← heq] at hlt
      exact (not_lt_of_ge (le_of_lt hmul)) hlt
    have hs :
        Function.support (FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)) =
          Metric.ball (0 : E) 2 := by
      simpa [FunctionalInequalities.Analysis.BakryEmery.unitBump] using
        (FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)).support_eq
    by_contra hne
    apply hnotball
    rw [← hs]
    exact hne
