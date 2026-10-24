-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_c_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:58:42.288181+00:00
-- url     : https://prove2.me/submissions/8a29215b-41c2-49ec-a4f7-d543b06e2488

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Generator
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_weighted_integral_quadraticExponent_of_compact_408915f

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- A tilted expectation as the ratio of prior integrals. -/
theorem FunctionalInequalities.Probability.Posterior.integral_tilted_eq_div {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    (φ f : Ω → ℝ) :
    (∫ x, f x ∂((μ : Measure Ω).tilted φ)) =
      (∫ x, Real.exp (φ x) * f x ∂(μ : Measure Ω)) / ∫ x, Real.exp (φ x) ∂(μ : Measure Ω) := by
  rw [integral_tilted]
  simp only [smul_eq_mul, div_mul_eq_mul_div]
  exact integral_div _ _
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
section Smooth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities.Probability.Posterior in
/-- The posterior expectation is `C^∞` in `c` at every fixed `Q`, including `Q = 0`. -/
theorem solution (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (Q : E →L[ℝ] E) :
    ContDiff ℝ ∞ (fun c => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ c Q f) := by
  have hN := FunctionalInequalities.Probability.Posterior.contDiff_weighted_integral_quadraticExponent_of_compact_408915f μ hc hf hC hfb Q
  have hZ := FunctionalInequalities.Probability.Posterior.contDiff_weighted_integral_quadraticExponent_of_compact_408915f μ hc (f := fun _ => (1 : ℝ)) measurable_const
    (C := 1) (by norm_num) (by intro x hx; simp) Q
  simp only [mul_one] at hZ
  have hpos (c : E) : (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) ∂(μ : Measure E)) ≠ 0 := by
    apply (integral_exp_pos (FunctionalInequalities.Probability.Posterior.integrable_exp_of_compact μ hc ?_)).ne'
    unfold FunctionalInequalities.Probability.Posterior.quadraticExponent
    fun_prop
  have heq : (fun c => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ c Q f) =
      fun c => (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) * f x ∂(μ : Measure E)) /
        ∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) ∂(μ : Measure E) := by
    funext c
    exact FunctionalInequalities.Probability.Posterior.integral_tilted_eq_div μ _ _
  rw [heq]
  exact hN.div hZ hpos
