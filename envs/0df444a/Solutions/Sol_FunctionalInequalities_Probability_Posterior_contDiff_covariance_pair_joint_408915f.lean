-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.contDiff_covariance_pair_joint_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:00:59.978766+00:00
-- url     : https://prove2.me/submissions/de70b5b6-8079-4da2-aa36-cf9e15f71c6a

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
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_JointRegularity
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
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorExpectation_joint_408915f

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
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]
/-- A measurable statistic bounded on the support is in `L²` of the tilt. -/
theorem FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact (μ : ProbabilityMeasure Ω) (hc : IsCompact (μ : Measure Ω).support)
    {φ f : Ω → ℝ} (hφ : Continuous φ) (hf : Measurable f) {C : ℝ}
    (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    MemLp f 2 ((μ : Measure Ω).tilted φ) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  apply (integrable_tilted_iff (integrable_exp_of_compact μ hc hφ) (fun x => f x ^ 2)).mpr
  have hd : Integrable (fun x => Real.exp (φ x) * f x ^ 2) (μ : Measure Ω) := by
    apply integrable_exp_mul_of_compact μ hc hφ (hf.pow_const 2) (C := C ^ 2) (sq_nonneg C)
    intro x hx
    rw [norm_pow]
    have hB : 0 ≤ C := (norm_nonneg (f x)).trans (hb x hx)
    exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb x hx)
  simpa only [smul_eq_mul] using hd
end
end
end
end
end

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
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
/-- Continuous statistics are in `L²` of every posterior of a compactly supported prior. -/
theorem FunctionalInequalities.Probability.Posterior.memLp_two_tilted_quadraticExponent_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E)
    {f : E → ℝ} (hf : Continuous f) :
    MemLp f 2 ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  obtain ⟨C, _hC, hb⟩ := exists_bound_on_support_of_compact μ hc hf
  have hφ : Continuous (quadraticExponent c Q) := by unfold quadraticExponent; fun_prop
  exact memLp_two_tilted_of_compact μ hc hφ hf.measurable hb
end
end
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory FunctionalInequalities
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
section Expectation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- A continuous statistic is bounded on the compact support, so its posterior expectation is jointly
`C^∞`. -/
theorem FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint_of_continuous (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {g : E → ℝ} (hg : Continuous g) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => posteriorExpectation μ p.1 p.2 g) := by
  obtain ⟨C, _hC, hb⟩ := exists_bound_on_support_of_compact μ hc hg
  exact contDiff_posteriorExpectation_joint_408915f μ hc hg.measurable hb
end Expectation
section Moments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities.Probability.Posterior in
/-- Covariances of two linear statistics under the posterior are jointly `C^∞` (polynomial moments of
the compact posterior). -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (u v : E) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
      covariance (fun x => ⟪u, x⟫) (fun x => ⟪v, x⟫)
        ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2))) := by
  have hs := FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint_of_continuous μ hc
    (g := fun x => ⟪u, x⟫ * ⟪v, x⟫) (by fun_prop)
  have hu := FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint_of_continuous μ hc (g := fun x => ⟪u, x⟫) (by fun_prop)
  have hv := FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint_of_continuous μ hc (g := fun x => ⟪v, x⟫) (by fun_prop)
  have he : (fun p : E × (E →L[ℝ] E) =>
      covariance (fun x => ⟪u, x⟫) (fun x => ⟪v, x⟫)
        ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2))) =
      (fun p => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ p.1 p.2 (fun x => ⟪u, x⟫ * ⟪v, x⟫)) -
        (fun p => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ p.1 p.2 (fun x => ⟪u, x⟫)) *
        (fun p => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ p.1 p.2 (fun x => ⟪v, x⟫)) := by
    funext p
    let : IsProbabilityMeasure ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2)) :=
      FunctionalInequalities.Probability.Posterior.isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc p.1 p.2
    rw [covariance_eq_sub
      (FunctionalInequalities.Probability.Posterior.memLp_two_tilted_quadraticExponent_of_compact μ hc p.1 p.2
        (by fun_prop : Continuous (fun x => ⟪u, x⟫)))
      (FunctionalInequalities.Probability.Posterior.memLp_two_tilted_quadraticExponent_of_compact μ hc p.1 p.2
        (by fun_prop : Continuous (fun x => ⟪v, x⟫)))]
    rfl
  rw [he]
  exact hs.sub (hu.mul hv)
