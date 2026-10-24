-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.scalar_brascamp_lieb_weak_finite_energy_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:45:09.257358+00:00
-- url     : https://prove2.me/submissions/d0be8cc8-1800-4869-b175-737b92ec2ad5

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Dissipation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Domain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_FormDomain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Smoothing
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Range
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.TaylorIntegral
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
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_centered_mem_closure_compactSmoothDiffusionImage_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_compact_weak_variational_estimate_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_inner_center_left_of_mean_zero_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_norm_sq_le_of_mem_closure_quadratic_bound_408915f

section
noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
variable {α : Type*} [MeasurableSpace α]
/-- The Hilbert-space mean agrees with the integral of any representative supplied by `Lp`. -/
theorem FunctionalInequalities.L2.mean_eq_integral (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ f = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [const_coeFn μ 1] with x hx
  simp [hx]
/-- Probability normalization makes the mean of a constant equal to that constant. -/
@[simp]
theorem FunctionalInequalities.L2.mean_const (μ : ProbabilityMeasure α) (c : ℝ) : mean μ (const μ c) = c := by
  rw [mean_eq_integral]
  calc
    (∫ x, const μ c x ∂(μ : Measure α)) = ∫ _ : α, c ∂(μ : Measure α) :=
      integral_congr_ae (const_coeFn μ c)
    _ = c := by simp
/-- The mean preserves subtraction. -/
@[simp]
theorem FunctionalInequalities.L2.mean_sub (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f - g) = mean μ f - mean μ g := by
  rw [mean, inner_sub_left]
  rfl
/-- The centered representative is pointwise `f - mean μ f` almost everywhere. -/
theorem FunctionalInequalities.L2.center_coeFn (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ f =ᵐ[(μ : Measure α)] fun x ↦ f x - mean μ f := by
  exact (Lp.coeFn_sub f (const μ (mean μ f))).trans
    (ae_eq_rfl.sub (const_coeFn μ (mean μ f)))
/-- A centered `L²` element has mean zero. -/
@[simp]
theorem FunctionalInequalities.L2.mean_center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (center μ f) = 0 := by
  simp [center]
/-- Coercing the `NNReal` variance to `ℝ` gives the squared norm of the centered part. -/
@[simp, norm_cast]
theorem FunctionalInequalities.L2.coe_variance (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ‖center μ f‖ ^ 2 := by
  rfl
/-- The intrinsic `L²` variance agrees, after coercion, with Mathlib's variance of the
representative supplied by the `Lp` element. -/
theorem FunctionalInequalities.L2.coe_variance_eq_pointwise (μ : ProbabilityMeasure α)
    (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ProbabilityTheory.variance f (μ : Measure α) := by
  rw [coe_variance, ← real_inner_self_eq_norm_sq (center μ f),
    MeasureTheory.L2.inner_def,
    ProbabilityTheory.variance_eq_integral (Lp.aestronglyMeasurable f).aemeasurable]
  apply integral_congr_ae
  filter_upwards [center_coeFn μ f] with x hx
  rw [hx, mean_eq_integral]
  simp [Real.norm_eq_abs]
/-- Taking the mean commutes with embedding a pointwise square-integrable function into `L²`. -/
theorem FunctionalInequalities.L2.mean_toLp (μ : ProbabilityMeasure α) {f : α → ℝ}
    (hf : MemLp f 2 (μ : Measure α)) :
    mean μ (hf.toLp f) = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean_eq_integral]
  exact integral_congr_ae hf.coeFn_toLp
end
end
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
section NormSquare
variable {V : Type*} [MeasurableSpace V]
/-- The `L²` norm squared of a square-integrable function is the integral of its squared norm. -/
theorem FunctionalInequalities.L2.norm_toLp_sq {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {μ : Measure V} {u : V → W} (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
end NormSquare
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology Set InnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.L2
open FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace LinearPMap
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
section
namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup
end FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.HeatSemigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- Every centered representative, including an arbitrary input after centering, has the same approximation property. -/
theorem FunctionalInequalities.KLS.LogConcave.HeatSemigroup.center_mem_closure_compactSmoothDiffusionImage
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
    (hν : FunctionalInequalities.KLS.LogConcave ν) {U : V → ℝ}
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (g : Lp ℝ 2 (ν : Measure V)) :
    L2.center ν g ∈ closure (compactSmoothDiffusionImage hU) := by
  exact centered_mem_closure_compactSmoothDiffusionImage_408915f m hν hνU hU
    (L2.center ν g) (L2.mean_center ν g)
end
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology Set InnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open scoped ContDiff RealInnerProductSpace
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
section RealL2
variable {α : Type*} [MeasurableSpace α]
/-- The scalar pairing of actual `toLp` classes is the integral of the
product of their original functions. -/
theorem FunctionalInequalities.KLS.LogConcave.real_inner_toLp {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ x, f x * g x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, mul_comm]
end RealL2
section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
omit [SecondCountableTopology E] in
/-- Every literal compact smooth diffusion image has mean zero, by compact
integration by parts against the constant function one. -/
theorem FunctionalInequalities.KLS.LogConcave.compact_diffusion_toLp_mean_zero
    {ν : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure]
    {U u : E → ℝ} (hνU : (ν : Measure E) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    FunctionalInequalities.L2.mean ν
      ((memLp_neg_weightedLaplacian (ν := ν) hU hu huc).toLp
        (fun x => -weightedLaplacian U u x)) = 0 := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hibp := integral_inner_gradient_tilted m
    (g := fun _ : E => (1 : ℝ)) hU hu2 huc contDiff_const
  rw [← hνU] at hibp
  rw [FunctionalInequalities.L2.mean_toLp]
  simpa only [gradient_fun_const, inner_zero_right, integral_zero, mul_one]
    using hibp.symm
end FiniteDimensional
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology Set InnerProductSpace Matrix
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open scoped ContDiff RealInnerProductSpace
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
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
set_option maxHeartbeats 2000000 in
/-- Weak finite-energy scalar Brascamp–Lieb inequality (Letwin arXiv:2607.24164v1 Lemma A.6 at C^{1,1}): for a
log-concave probability `ν = e^{-U} dx` with `U` C1, globally Lipschitz, with Lipschitz gradient and a.e. positive
definite coordinate Hessian, and a globally bounded weak test `η` with integrable inverse-Hessian energy,
`Var_ν η ≤ ∫ ⟪a, (∇²U)⁻¹ a⟫ dν`. -/
theorem solution {n : ℕ}
    {nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hnu : FunctionalInequalities.KLS.LogConcave nu)
    {U eta : EuclideanSpace ℝ (Fin n) → ℝ}
    (hnuU : (nu : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))
    (hU : ContDiff ℝ 1 U) {G : NNReal} (hG : LipschitzWith G (gradient U))
    {L : NNReal} (hL : LipschitzWith L U)
    (hnorm : (∫ x, Real.exp (-U x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (FunctionalInequalities.Probability.Stein.hessianMatrix U x).PosDef)
    (a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ)
    (heta : LocallyIntegrable eta (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖eta x‖ ≤ C)
    (hweak : ∀ i : Fin n, FunctionalInequalities.Analysis.HasWeakDerivAlong eta (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (henergy : Integrable (fun x => (fun i => a i x) ⬝ᵥ
      ((FunctionalInequalities.Probability.Stein.hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x))) (nu : Measure (EuclideanSpace ℝ (Fin n)))) :
    ProbabilityTheory.variance eta (nu : Measure (EuclideanSpace ℝ (Fin n))) ≤
      ∫ x, (fun i => a i x) ⬝ᵥ ((FunctionalInequalities.Probability.Stein.hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x))
        ∂(nu : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hac : (nu : Measure (EuclideanSpace ℝ (Fin n))) ≪
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [hnuU]
    exact tilted_absolutelyContinuous _ _
  have heta2 : MemLp eta 2 (nu : Measure (EuclideanSpace ℝ (Fin n))) :=
    MemLp.of_bound (heta.aestronglyMeasurable.mono_ac hac) C (Filter.Eventually.of_forall hbound)
  let F : Lp ℝ 2 (nu : Measure (EuclideanSpace ℝ (Fin n))) := heta2.toLp eta
  let D : ℝ := ∫ x, (fun i => a i x) ⬝ᵥ ((FunctionalInequalities.Probability.Stein.hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x))
    ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))
  have hQ : ∀ w ∈ FunctionalInequalities.KLS.LogConcave.HeatSemigroup.compactSmoothDiffusionImage (ν := nu) hU,
      2 * ⟪FunctionalInequalities.L2.center nu F, w⟫ - ‖w‖ ^ 2 ≤ D := by
    rintro w ⟨v, hv, hvc, rfl⟩
    let hLap : MemLp (fun x => -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x) 2 (nu : Measure (EuclideanSpace ℝ (Fin n))) :=
      FunctionalInequalities.KLS.LogConcave.memLp_neg_weightedLaplacian (ν := nu) hU hv hvc
    let V : Lp ℝ 2 (nu : Measure (EuclideanSpace ℝ (Fin n))) := hLap.toLp (fun x => -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x)
    change 2 * ⟪FunctionalInequalities.L2.center nu F, V⟫ - ‖V‖ ^ 2 ≤ D
    have hmean : FunctionalInequalities.L2.mean nu V = 0 :=
      FunctionalInequalities.KLS.LogConcave.compact_diffusion_toLp_mean_zero volume hnuU hU hv hvc
    have hinner : ⟪F, V⟫ = ∫ x, eta x * (-FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x)
        ∂(nu : Measure (EuclideanSpace ℝ (Fin n))) := FunctionalInequalities.KLS.LogConcave.real_inner_toLp heta2 hLap
    have hnormV : ‖V‖ ^ 2 = ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x ^ 2
        ∂(nu : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [V, Real.norm_eq_abs, abs_neg, sq_abs] using FunctionalInequalities.L2.norm_toLp_sq hLap
    rw [FunctionalInequalities.KLS.LogConcave.inner_center_left_of_mean_zero_408915f nu F V hmean, hinner, hnormV]
    exact (FunctionalInequalities.KLS.LogConcave.compact_weak_variational_estimate_408915f hnuU hU hG hL hnorm hPD a C heta hbound hweak ha2 henergy hv hvc).2.2
  have hclosure : FunctionalInequalities.L2.center nu F ∈ closure (FunctionalInequalities.KLS.LogConcave.HeatSemigroup.compactSmoothDiffusionImage (ν := nu) hU) :=
    FunctionalInequalities.KLS.LogConcave.HeatSemigroup.center_mem_closure_compactSmoothDiffusionImage volume hnu hnuU hU F
  have hnormF : ‖FunctionalInequalities.L2.center nu F‖ ^ 2 ≤ D :=
    FunctionalInequalities.KLS.LogConcave.norm_sq_le_of_mem_closure_quadratic_bound_408915f (FunctionalInequalities.L2.center nu F) hclosure hQ
  have hvariance : (FunctionalInequalities.L2.variance nu F : ℝ) =
      ProbabilityTheory.variance eta (nu : Measure (EuclideanSpace ℝ (Fin n))) :=
    (FunctionalInequalities.L2.coe_variance_eq_pointwise nu F).trans (ProbabilityTheory.variance_congr heta2.coeFn_toLp)
  rw [← hvariance, FunctionalInequalities.L2.coe_variance]
  exact hnormF
