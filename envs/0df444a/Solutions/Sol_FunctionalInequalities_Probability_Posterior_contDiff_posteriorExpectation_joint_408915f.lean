-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:59:44.947747+00:00
-- url     : https://prove2.me/submissions/4b5b6165-9bc3-436e-a55d-d61b5e24d605

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
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorExpectation_c_408915f

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
section Chart
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E] in
private theorem FunctionalInequalities.Probability.Posterior.parameterScore_apply (x : E) (p : E × (E →L[ℝ] E)) :
    FunctionalInequalities.Probability.Posterior.parameterScore E x p = quadraticExponent p.1 p.2 x := by
  change ⟪x, p.1⟫ - (1 / 2 : ℝ) * ⟪x, p.2 x⟫ = quadraticExponent p.1 p.2 x
  simp only [quadraticExponent]
  rw [real_inner_comm x p.1, real_inner_comm x (p.2 x)]
private theorem FunctionalInequalities.Probability.Posterior.parameterFeature_pairing (p : E × (E →L[ℝ] E)) (x : E) :
    ⟪FunctionalInequalities.Probability.Posterior.parameterChart E p, FunctionalInequalities.Probability.Posterior.parameterFeature E x⟫ = quadraticExponent p.1 p.2 x := by
  rw [real_inner_comm]
  unfold FunctionalInequalities.Probability.Posterior.parameterFeature
  rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply, parameterScore_apply]
private theorem FunctionalInequalities.Probability.Posterior.parameterRetract_feature (x : E) :
    FunctionalInequalities.Probability.Posterior.parameterRetract E (FunctionalInequalities.Probability.Posterior.parameterFeature E x) = x := by
  apply ext_inner_left ℝ
  intro c
  rw [FunctionalInequalities.Probability.Posterior.parameterRetract, ContinuousLinearMap.adjoint_inner_right]
  have h := parameterFeature_pairing E (c, 0) x
  simp only [quadraticExponent, zero_apply, inner_zero_left, mul_zero,
    sub_zero] at h
  change ⟪FunctionalInequalities.Probability.Posterior.parameterChart E (c, 0), FunctionalInequalities.Probability.Posterior.parameterFeature E x⟫ = ⟪c, x⟫
  convert! h using 1
end Chart
section Expectation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
private theorem FunctionalInequalities.Probability.Posterior.featureLaw_support_subset (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    (FunctionalInequalities.Probability.Posterior.featureLaw μ : Measure (FunctionalInequalities.Probability.Posterior.parameterSpace E)).support ⊆
      FunctionalInequalities.Probability.Posterior.parameterFeature E '' (μ : Measure E).support := by
  have hk : IsCompact (FunctionalInequalities.Probability.Posterior.parameterFeature E '' (μ : Measure E).support) :=
    hc.image (FunctionalInequalities.Probability.Posterior.continuous_parameterFeature E)
  have ha : FunctionalInequalities.Probability.Posterior.parameterFeature E '' (μ : Measure E).support ∈ ae (FunctionalInequalities.Probability.Posterior.featureLaw μ : Measure (FunctionalInequalities.Probability.Posterior.parameterSpace E)) := by
    rw [mem_ae_iff]
    change ((μ : Measure E).map (FunctionalInequalities.Probability.Posterior.parameterFeature E))
      (FunctionalInequalities.Probability.Posterior.parameterFeature E '' (μ : Measure E).support)ᶜ = 0
    rw [Measure.map_apply (FunctionalInequalities.Probability.Posterior.continuous_parameterFeature E).measurable
      hk.isClosed.measurableSet.compl]
    apply measure_mono_null ?_ (μ : Measure E).measure_compl_support
    intro x hx hxS
    exact hx ⟨x, hxS, rfl⟩
  exact Measure.support_subset_of_isClosed hk.isClosed ha
private theorem FunctionalInequalities.Probability.Posterior.featureLaw_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    IsCompact (FunctionalInequalities.Probability.Posterior.featureLaw μ : Measure (FunctionalInequalities.Probability.Posterior.parameterSpace E)).support :=
  (hc.image (FunctionalInequalities.Probability.Posterior.continuous_parameterFeature E)).of_isClosed_subset
    (FunctionalInequalities.Probability.Posterior.featureLaw μ : Measure (FunctionalInequalities.Probability.Posterior.parameterSpace E)).isClosed_support (featureLaw_support_subset μ hc)
private theorem FunctionalInequalities.Probability.Posterior.feature_statistic_bound (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support)
    {f : E → ℝ} {C : ℝ} (hb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) :
    ∀ y ∈ (FunctionalInequalities.Probability.Posterior.featureLaw μ : Measure (FunctionalInequalities.Probability.Posterior.parameterSpace E)).support, ‖(f ∘ FunctionalInequalities.Probability.Posterior.parameterRetract E) y‖ ≤ C := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := featureLaw_support_subset μ hc hy
  simpa only [Function.comp_apply, parameterRetract_feature] using hb x hx
/-- The joint posterior expectation is the `c`-only expectation of the feature law at `Q' = 0`, with
both the numerator and the normalising integral transported. -/
private theorem FunctionalInequalities.Probability.Posterior.posteriorExpectation_feature (μ : ProbabilityMeasure E) {f : E → ℝ}
    (hf : Measurable f) (p : E × (E →L[ℝ] E)) :
    posteriorExpectation μ p.1 p.2 f =
      posteriorExpectation (FunctionalInequalities.Probability.Posterior.featureLaw μ) (FunctionalInequalities.Probability.Posterior.parameterChart E p) 0 (f ∘ FunctionalInequalities.Probability.Posterior.parameterRetract E) := by
  have hphase (x : E) : quadraticExponent (FunctionalInequalities.Probability.Posterior.parameterChart E p) (0 : _ →L[ℝ] _)
      (FunctionalInequalities.Probability.Posterior.parameterFeature E x) = quadraticExponent p.1 p.2 x := by
    simpa only [quadraticExponent, zero_apply, inner_zero_left, mul_zero,
      sub_zero] using parameterFeature_pairing E p x
  have hp : Continuous (quadraticExponent (FunctionalInequalities.Probability.Posterior.parameterChart E p) (0 : _ →L[ℝ] _)) := by
    unfold quadraticExponent
    fun_prop
  have hf' : Measurable (f ∘ FunctionalInequalities.Probability.Posterior.parameterRetract E) :=
    hf.comp (FunctionalInequalities.Probability.Posterior.parameterRetract E).continuous.measurable
  have hN :
      (∫ y, Real.exp (quadraticExponent (FunctionalInequalities.Probability.Posterior.parameterChart E p) 0 y) * (f ∘ FunctionalInequalities.Probability.Posterior.parameterRetract E) y
        ∂(FunctionalInequalities.Probability.Posterior.featureLaw μ : Measure (FunctionalInequalities.Probability.Posterior.parameterSpace E))) =
        ∫ x, Real.exp (quadraticExponent p.1 p.2 x) * f x ∂(μ : Measure E) := by
    have h := integral_map (μ := (μ : Measure E))
      (FunctionalInequalities.Probability.Posterior.continuous_parameterFeature E).measurable.aemeasurable
      (hp.measurable.exp.mul hf').aestronglyMeasurable
    simpa only [FunctionalInequalities.Probability.Posterior.featureLaw, ProbabilityMeasure.toMeasure_map, Function.comp_apply,
      Pi.mul_apply, hphase, parameterRetract_feature] using h
  have hZ :
      (∫ y, Real.exp (quadraticExponent (FunctionalInequalities.Probability.Posterior.parameterChart E p) 0 y) ∂(FunctionalInequalities.Probability.Posterior.featureLaw μ : Measure (FunctionalInequalities.Probability.Posterior.parameterSpace E))) =
        ∫ x, Real.exp (quadraticExponent p.1 p.2 x) ∂(μ : Measure E) := by
    have h := integral_map (μ := (μ : Measure E))
      (FunctionalInequalities.Probability.Posterior.continuous_parameterFeature E).measurable.aemeasurable
      hp.measurable.exp.aestronglyMeasurable
    simpa only [FunctionalInequalities.Probability.Posterior.featureLaw, ProbabilityMeasure.toMeasure_map, hphase] using h
  unfold posteriorExpectation
  rw [integral_tilted_eq_div μ, integral_tilted_eq_div (FunctionalInequalities.Probability.Posterior.featureLaw μ), hN, hZ]
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities.Probability.Posterior in
/-- **Joint smoothness of the posterior expectation** (BKL (67), compact stage): for a compactly
supported prior and a measurable `f` bounded on the prior support, `(c, Q) ↦ ∫ f dμ_{c,Q}` is `C^∞` on
`E × (E →L[ℝ] E)`; every finite pair, including `Q = 0`, non-symmetric `Q` and dimension zero. `f` may be
discontinuous or unbounded off the support. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ p.1 p.2 f) := by
  have hbound : ∀ y ∈ (FunctionalInequalities.Probability.Posterior.featureLaw μ : Measure (FunctionalInequalities.Probability.Posterior.parameterSpace E)).support,
      ‖(f ∘ FunctionalInequalities.Probability.Posterior.parameterRetract E) y‖ ≤ max C 0 := by
    intro y hy
    exact (feature_statistic_bound μ hc hb y hy).trans (le_max_left C 0)
  have hsm := FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_c_408915f (FunctionalInequalities.Probability.Posterior.featureLaw μ) (featureLaw_compact μ hc)
    (hf.comp (FunctionalInequalities.Probability.Posterior.parameterRetract E).continuous.measurable) (le_max_right C 0) hbound
    (0 : _ →L[ℝ] _)
  have hcom := hsm.comp (FunctionalInequalities.Probability.Posterior.parameterChart E).contDiff
  have he : (fun p : E × (E →L[ℝ] E) => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ p.1 p.2 f) =
      (fun c => FunctionalInequalities.Probability.Posterior.posteriorExpectation (FunctionalInequalities.Probability.Posterior.featureLaw μ) c 0 (f ∘ FunctionalInequalities.Probability.Posterior.parameterRetract E)) ∘
        FunctionalInequalities.Probability.Posterior.parameterChart E := by
    funext p
    exact posteriorExpectation_feature μ hf p
  rw [he]
  exact hcom
