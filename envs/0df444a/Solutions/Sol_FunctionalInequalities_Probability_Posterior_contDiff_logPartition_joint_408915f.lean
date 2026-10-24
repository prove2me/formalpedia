-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.contDiff_logPartition_joint_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:07:44.17899+00:00
-- url     : https://prove2.me/submissions/b58a395a-3edb-4f41-92a0-d3b16abb285a

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
omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Probability.Posterior.partitionParameterScore_apply (x : E)
    (p : E × (E →L[ℝ] E)) :
    FunctionalInequalities.Probability.Posterior.partitionParameterScore x p = quadraticExponent p.1 p.2 x := by
  change ⟪x, p.1⟫ - (1 / 2 : ℝ) * ⟪x, p.2 x⟫ =
    quadraticExponent p.1 p.2 x
  simp only [quadraticExponent]
  rw [real_inner_comm x p.1, real_inner_comm x (p.2 x)]
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Probability.Posterior.partitionParameterFeature_pairing
    (p : E × (E →L[ℝ] E)) (x : E) :
    ⟪FunctionalInequalities.Probability.Posterior.partitionParameterChart p, FunctionalInequalities.Probability.Posterior.partitionParameterFeature x⟫ =
      quadraticExponent p.1 p.2 x := by
  rw [real_inner_comm]
  unfold FunctionalInequalities.Probability.Posterior.partitionParameterFeature
  rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    partitionParameterScore_apply]
omit [CompleteSpace E] in
private theorem FunctionalInequalities.Probability.Posterior.partitionLaw_support_subset (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    (FunctionalInequalities.Probability.Posterior.partitionLaw μ : Measure (FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E))).support ⊆
      FunctionalInequalities.Probability.Posterior.partitionParameterFeature (E := E) '' (μ : Measure E).support := by
  have hk : IsCompact
      (FunctionalInequalities.Probability.Posterior.partitionParameterFeature (E := E) '' (μ : Measure E).support) :=
    hc.image (FunctionalInequalities.Probability.Posterior.partitionParameterFeature_continuous (E := E))
  have ha : FunctionalInequalities.Probability.Posterior.partitionParameterFeature (E := E) '' (μ : Measure E).support ∈
      ae (FunctionalInequalities.Probability.Posterior.partitionLaw μ : Measure (FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E))) := by
    rw [mem_ae_iff]
    change ((μ : Measure E).map (FunctionalInequalities.Probability.Posterior.partitionParameterFeature (E := E)))
      (FunctionalInequalities.Probability.Posterior.partitionParameterFeature (E := E) '' (μ : Measure E).support)ᶜ = 0
    rw [Measure.map_apply (FunctionalInequalities.Probability.Posterior.partitionParameterFeature_continuous (E := E)).measurable
      hk.isClosed.measurableSet.compl]
    apply measure_mono_null ?_ (μ : Measure E).measure_compl_support
    intro x hx hxS
    exact hx ⟨x, hxS, rfl⟩
  exact Measure.support_subset_of_isClosed hk.isClosed ha
omit [CompleteSpace E] in
private theorem FunctionalInequalities.Probability.Posterior.partitionLaw_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    IsCompact
      (FunctionalInequalities.Probability.Posterior.partitionLaw μ : Measure (FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E))).support :=
  (hc.image (FunctionalInequalities.Probability.Posterior.partitionParameterFeature_continuous (E := E))).of_isClosed_subset
    (FunctionalInequalities.Probability.Posterior.partitionLaw μ : Measure (FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E))).isClosed_support
    (partitionLaw_support_subset μ hc)
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities.Probability.Posterior in
omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- `ψ` is jointly `C^∞` in `(c, Q)` for a compactly supported prior. -/
theorem solution
    [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => FunctionalInequalities.Probability.Posterior.logPartition μ p.1 p.2) := by
  have hexp : ∀ r : ℝ,
      Integrable
        (fun y : FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E) =>
          Real.exp (r * ‖y‖))
        (FunctionalInequalities.Probability.Posterior.partitionLaw μ : Measure (FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E))) := by
    intro r
    exact FunctionalInequalities.Probability.Posterior.integrable_exp_of_compact (FunctionalInequalities.Probability.Posterior.partitionLaw μ) (partitionLaw_compact μ hc)
      (by fun_prop)
  have hsm :
      ContDiff ℝ ∞
        (fun z : FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E) =>
          ∫ y, Real.exp ⟪z, y⟫
            ∂(FunctionalInequalities.Probability.Posterior.partitionLaw μ : Measure (FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E)))) := by
    simpa only [smul_eq_mul, mul_one] using
      (FunctionalInequalities.Analysis.BakryEmery.contDiff_integral_exp_inner_smul
        (FunctionalInequalities.Probability.Posterior.partitionLaw μ : Measure (FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E))) hexp
        (g := fun _ : FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E) => (1 : ℝ))
        (M := 1) (k := 0)
        (hg := measurable_const.aestronglyMeasurable)
        (hgb := by
          intro y
          simp))
  have heq :
      (fun p : E × (E →L[ℝ] E) =>
        ∫ y, Real.exp ⟪FunctionalInequalities.Probability.Posterior.partitionParameterChart p, y⟫
          ∂(FunctionalInequalities.Probability.Posterior.partitionLaw μ : Measure (FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E)))) =
      (fun p : E × (E →L[ℝ] E) =>
        ∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2 x)
          ∂(μ : Measure E)) := by
    funext p
    have hp : Continuous
        (fun y : FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E) =>
          Real.exp ⟪FunctionalInequalities.Probability.Posterior.partitionParameterChart p, y⟫) := by
      fun_prop
    have h := integral_map (μ := (μ : Measure E))
      (FunctionalInequalities.Probability.Posterior.partitionParameterFeature_continuous (E := E)).measurable.aemeasurable
      (hp.measurable.aestronglyMeasurable)
    simpa only [FunctionalInequalities.Probability.Posterior.partitionLaw, ProbabilityMeasure.toMeasure_map,
      Function.comp_apply, partitionParameterFeature_pairing] using h
  have hcomp :
      ContDiff ℝ ∞
        (fun p : E × (E →L[ℝ] E) =>
          ∫ y, Real.exp ⟪FunctionalInequalities.Probability.Posterior.partitionParameterChart p, y⟫
            ∂(FunctionalInequalities.Probability.Posterior.partitionLaw μ : Measure (FunctionalInequalities.Probability.Posterior.partitionParameterSpace (E := E)))) := by
    convert hsm.comp (FunctionalInequalities.Probability.Posterior.partitionParameterChart (E := E)).contDiff using 1
    rfl
  have hZ :
      ContDiff ℝ ∞
        (fun p : E × (E →L[ℝ] E) =>
          ∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2 x)
            ∂(μ : Measure E)) := by
    rw [heq] at hcomp
    exact hcomp
  have hpos : ∀ p : E × (E →L[ℝ] E),
      0 < ∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2 x)
        ∂(μ : Measure E) := by
    intro p
    exact integral_exp_pos
      (FunctionalInequalities.Probability.Posterior.integrable_exp_of_compact μ hc (by
        unfold FunctionalInequalities.Probability.Posterior.quadraticExponent
        fun_prop))
  have hlog := hZ.log (fun p => (hpos p).ne')
  simpa only [FunctionalInequalities.Probability.Posterior.logPartition] using hlog
