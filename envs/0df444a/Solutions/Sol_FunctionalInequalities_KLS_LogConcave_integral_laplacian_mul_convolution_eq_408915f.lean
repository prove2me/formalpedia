-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.integral_laplacian_mul_convolution_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:33:29.418743+00:00
-- url     : https://prove2.me/submissions/b0bc0f4a-ee0e-4076-9450-11e42ec15cea

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_gradient_convolution_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_integral_inner_convolution_eq_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_laplacian_convolution_408915f

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Mollification
open scoped ContDiff RealInnerProductSpace Convolution ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
open Energy Energy.WeightedGradient
section Pointwise
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]
/-- The Laplacian vanishes outside the closed support. -/
private theorem FunctionalInequalities.KLS.LogConcave.laplacian_eq_zero_of_notMem_tsupport {f : V → ℝ} {y : V} (hy : y ∉ tsupport f) :
    Laplacian.laplacian f y = 0 := by
  have h2 : fderiv ℝ (fderiv ℝ f) y = 0 := by
    by_contra h
    exact hy (tsupport_fderiv_subset (𝕜 := ℝ) (support_fderiv_subset (𝕜 := ℝ) h))
  rw [laplacian_eq_sum_fderiv_fderiv, h2]
  simp
variable [CompleteSpace V]
omit [FiniteDimensional ℝ V] in
/-- The gradient vanishes outside the closed support. -/
private theorem FunctionalInequalities.KLS.LogConcave.gradient_eq_zero_of_notMem_tsupport {f : V → ℝ} {y : V} (hy : y ∉ tsupport f) :
    gradient f y = 0 := by
  have h : fderiv ℝ f y = 0 := by
    by_contra h
    exact hy (support_fderiv_subset (𝕜 := ℝ) h)
  rw [gradient, h, map_zero]
end Pointwise
section Haar
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (m : Measure V) [m.IsAddHaarMeasure]
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- **The mollified weak equation.** If `W` satisfies the weak equation
`∫ Δf W = ∫ ⟪∇f, W F⟫ + ∫ f W` against every smooth compactly supported `f`, `η` is a bump equal
to one on `closedBall 0 (R + 1)`, and `ρ` is a normalised bump of radius at most one, then the
mollifications `v = ρ ⋆ (η W)` and `H = ρ ⋆ (η W F)` satisfy the same equation against every
smooth test supported in `closedBall 0 R`. The mollifier is moved onto the test function by the
symmetry identity, commuted with `Δ` and `∇`, and the cutoff `η` is invisible where the mollified
test lives. -/
 theorem solution {W : V → ℝ} {F : V → V}
    (hW : ∀ f : V → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∫ x, Laplacian.laplacian f x * W x ∂m =
        ∫ x, ⟪gradient f x, W x • F x⟫ ∂m + ∫ x, f x * W x ∂m)
    {R : ℝ} (η : ContDiffBump (0 : V)) (hη : R + 1 ≤ η.rIn)
    (hw : Integrable (fun x => η x * W x) m) (hG : Integrable (fun x => (η x * W x) • F x) m)
    (φ : ContDiffBump (0 : V)) (hφ : φ.rOut ≤ 1) {g : V → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hgR : tsupport g ⊆ closedBall 0 R) :
    ∫ x, Laplacian.laplacian g x *
        (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m =
      ∫ x, ⟪gradient g x,
          (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => (η y * W y) • F y) x⟫ ∂m +
        ∫ x, g x * (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg2 : ContDiff ℝ 2 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hρloc : LocallyIntegrable (φ.normed m) m := φ.integrable_normed.locallyIntegrable
  -- the mollified test function
  set f : V → ℝ := φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g with hf_def
  have hf : ContDiff ℝ ∞ f :=
    HasCompactSupport.contDiff_convolution_left _ (φ.hasCompactSupport_normed (μ := m))
      φ.contDiff_normed hg1.continuous.locallyIntegrable
  have hfc : HasCompactSupport f :=
    HasCompactSupport.convolution _ (φ.hasCompactSupport_normed (μ := m)) hgc
  have hfsupp : tsupport f ⊆ closedBall 0 (R + 1) := by
    refine closure_minimal ?_ isClosed_closedBall
    refine (support_convolution_subset _).trans ?_
    rintro x ⟨a, ha, b, hb, rfl⟩
    rw [φ.support_normed_eq, mem_ball, dist_zero_right] at ha
    have hb' : ‖b‖ ≤ R := by
      have := hgR (subset_tsupport _ hb)
      rwa [mem_closedBall, dist_zero_right] at this
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_add_le a b]
  have hη1 : ∀ x ∈ tsupport f, η x = 1 := fun x hx =>
    η.one_of_mem_closedBall (closedBall_subset_closedBall hη (hfsupp hx))
  -- the derivatives of the mollified test
  have hlap : ∀ x, Laplacian.laplacian f x =
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] Laplacian.laplacian g) x :=
    FunctionalInequalities.Analysis.Mollification.laplacian_convolution_408915f φ hg hgc
  have hgrad : ∀ x, gradient f x = (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] gradient g) x :=
    FunctionalInequalities.Analysis.Mollification.gradient_convolution_408915f φ hg hgc
  -- the weak equation for `f`
  have hWf := hW f hf hfc
  -- (i) the Laplacian term
  have e1 : ∫ x, Laplacian.laplacian g x *
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m =
      ∫ x, Laplacian.laplacian f x * W x ∂m := by
    have h := FunctionalInequalities.Analysis.Mollification.integral_inner_convolution_eq_408915f (E := ℝ) φ hw (FunctionalInequalities.Analysis.BakryEmery.continuous_laplacian hg2)
      (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_laplacian hgc)
    simp only [Real.inner_apply] at h
    rw [show (∫ x, Laplacian.laplacian g x *
        (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m) =
        ∫ x, (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x *
          Laplacian.laplacian g x ∂m from
        integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _), h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [← hlap]
    by_cases hx : x ∈ tsupport f
    · rw [hη1 x hx]; ring
    · rw [laplacian_eq_zero_of_notMem_tsupport hx]; ring
  -- (ii) the gradient term
  have e2 : ∫ x, ⟪gradient f x, W x • F x⟫ ∂m = ∫ x, ⟪gradient g x,
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => (η y * W y) • F y) x⟫ ∂m := by
    have h := FunctionalInequalities.Analysis.Mollification.integral_inner_convolution_eq_408915f (E := V) φ hG (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hg1)
      (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gradient hgc)
    rw [show (∫ x, ⟪gradient g x,
        (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => (η y * W y) • F y) x⟫ ∂m) =
        ∫ x, ⟪(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => (η y * W y) • F y) x,
          gradient g x⟫ ∂m from
        integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_comm _ _), h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    by_cases hx : x ∈ tsupport f
    · rw [hgrad, hη1 x hx, one_mul, real_inner_comm]
    · rw [gradient_eq_zero_of_notMem_tsupport hx, inner_zero_left, ← hgrad,
        gradient_eq_zero_of_notMem_tsupport hx, inner_zero_right]
  -- (iii) the zeroth-order term
  have e3 : ∫ x, f x * W x ∂m =
      ∫ x, g x * (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m := by
    have h := FunctionalInequalities.Analysis.Mollification.integral_inner_convolution_eq_408915f (E := ℝ) φ hw hg1.continuous hgc
    simp only [Real.inner_apply] at h
    rw [show (∫ x, g x * (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m)
        = ∫ x, (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x * g x ∂m from
        integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _), h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show f x * W x = η x * W x * f x
    by_cases hx : x ∈ tsupport f
    · rw [hη1 x hx]; ring
    · rw [image_eq_zero_of_notMem_tsupport hx]; ring
  rw [e1, hWf, e2, e3]
