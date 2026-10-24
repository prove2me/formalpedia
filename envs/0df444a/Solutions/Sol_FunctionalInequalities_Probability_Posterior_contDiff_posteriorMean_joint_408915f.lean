-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.contDiff_posteriorMean_joint_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:01:01.760978+00:00
-- url     : https://prove2.me/submissions/e8e21573-cd0a-4d53-9f13-59cbc6fa4d05

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
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_408915f

section
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
section Mean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- `∫ ⟪h, x⟫ dμ_{c,Q} = ⟪h, a⟫` (finite second moment from compact support). -/
theorem FunctionalInequalities.Probability.Posterior.integral_inner_eq_inner_posteriorMean (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) (h : E) :
    (∫ x, ⟪h, x⟫ ∂((μ : Measure E).tilted (quadraticExponent c Q))) = ⟪h, posteriorMean μ c Q⟫ := by
  obtain ⟨R, _hR, hmom⟩ := exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_408915f μ hc
  let : IsProbabilityMeasure ((μ : Measure E).tilted (quadraticExponent c Q)) := isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc c Q
  have h2 : MemLp id 2 ((μ : Measure E).tilted (quadraticExponent c Q)) :=
    (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).mpr (hmom c Q 2).1
  have hi := h2.integrable one_le_two
  change (∫ x, (innerSL ℝ h) (id x) ∂((μ : Measure E).tilted (quadraticExponent c Q))) =
    (innerSL ℝ h) (∫ x, id x ∂((μ : Measure E).tilted (quadraticExponent c Q)))
  exact (innerSL ℝ h).integral_comp_comm hi
variable {ι : Type*} [Fintype ι]
end Mean
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
/-- The posterior mean `a(c,Q) = ∫ x dμ_{c,Q}` is jointly `C^∞` (reconstructed from its coordinates in an
orthonormal basis). -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2) := by
  let b := stdOrthonormalBasis ℝ E
  have hs (i : Fin (Module.finrank ℝ E)) :
      ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
        FunctionalInequalities.Probability.Posterior.posteriorExpectation μ p.1 p.2 (fun x => ⟪b i, x⟫)) :=
    FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint_of_continuous μ hc (by fun_prop)
  have hm : ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
      ∑ i, FunctionalInequalities.Probability.Posterior.posteriorExpectation μ p.1 p.2 (fun x => ⟪b i, x⟫) • b i) :=
    ContDiff.sum (fun i _hi => (hs i).smul contDiff_const)
  have he : (fun p : E × (E →L[ℝ] E) => FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2) =
      fun p => ∑ i, FunctionalInequalities.Probability.Posterior.posteriorExpectation μ p.1 p.2 (fun x => ⟪b i, x⟫) • b i := by
    funext p
    rw [← b.sum_repr' (FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2)]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← FunctionalInequalities.Probability.Posterior.integral_inner_eq_inner_posteriorMean μ hc p.1 p.2 (b i)]
    rfl
  rw [he]
  exact hm
