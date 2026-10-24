-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.logLaplace_compactPosterior_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:08:00.809383+00:00
-- url     : https://prove2.me/submissions/e979fe64-f11d-4750-947e-47eedb28c440

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_JointRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_LogPartition
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
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
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
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
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.Variance

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
open MeasureTheory ProbabilityTheory
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities.Probability.Posterior in
omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
theorem solution
    [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) (z : E) :
    FunctionalInequalities.Analysis.BakryEmery.logLaplace (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc c Q : Measure E) z =
      FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q - FunctionalInequalities.Probability.Posterior.logPartition μ c Q := by
  unfold FunctionalInequalities.Analysis.BakryEmery.logLaplace
  change Real.log
      (∫ x, Real.exp ⟪z, x⟫
        ∂((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q))) =
      FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q - FunctionalInequalities.Probability.Posterior.logPartition μ c Q
  rw [FunctionalInequalities.Probability.Posterior.integral_tilted_eq_div]
  have heq :
      (fun x : E =>
        Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) * Real.exp ⟪z, x⟫) =
      (fun x : E => Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent (c + z) Q x)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    simp only [FunctionalInequalities.Probability.Posterior.quadraticExponent, inner_add_left]
    ring
  rw [heq]
  simp only [FunctionalInequalities.Probability.Posterior.logPartition]
  rw [Real.log_div
    (integral_exp_pos
      (FunctionalInequalities.Probability.Posterior.integrable_exp_of_compact μ hc (by
        unfold FunctionalInequalities.Probability.Posterior.quadraticExponent
        fun_prop))).ne'
    (integral_exp_pos
      (FunctionalInequalities.Probability.Posterior.integrable_exp_of_compact μ hc (by
        unfold FunctionalInequalities.Probability.Posterior.quadraticExponent
        fun_prop))).ne']
