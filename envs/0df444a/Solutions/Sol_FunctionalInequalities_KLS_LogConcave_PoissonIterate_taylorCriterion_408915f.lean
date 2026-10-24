-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorCriterion_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:06:22.591391+00:00
-- url     : https://prove2.me/submissions/04ab13dd-64a7-43a5-9234-c2de1c2578c9

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Dirichlet
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Quadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Criterion
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Permutation
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_TaylorRecursion
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Hessian
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Markov
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Ambient
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Const
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
import Mathlib.Analysis.Distribution.TemperateGrowth
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
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.MeanInequalities
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
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
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
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_hessianSq_add_le_of_hasTemperateGrowth_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_summable_and_tendsto_zero_of_energy_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_const_mul_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_inv_le_scale_sq_step_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_le_of_iterate_bounds_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_meanGradSq_eq_norm_taylorField_one_genField_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_normSq_gradField_gradField_step_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_norm_taylorField_grad0_iter_sq_le_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_norm_taylorField_sq_le_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_sum_mean_partialDeriv_sq_le_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_id_gap_of_literature_le_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_convexOn_of_eq_tilted_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_existsUnique_centered_adjointComp_eq_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_centered_approx_eigenfunction_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_weakHessian_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_literatureConstant_le_inv_of_tendsto_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_tendsto_norm_center_apply_408915f
import Theorems.Thm_FunctionalInequalities_L2_inner_center_center_408915f
import Theorems.Thm_FunctionalInequalities_L2_sum_norm_sq_compLp_innerSL_408915f

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
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
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section StdBasis
variable [FiniteDimensional ℝ E]
variable [CompleteSpace E]
/-- `‖∇f‖²` is the sum of the squared directional derivatives in the standard orthonormal basis. -/
theorem FunctionalInequalities.Analysis.BakryEmery.norm_gradient_sq_eq_sum (f : E → ℝ) (y : E) :
    ‖gradient f y‖ ^ 2 = ∑ i, fderiv ℝ f y (stdOrthonormalBasis ℝ E i) ^ 2 := by
  rw [← (stdOrthonormalBasis ℝ E).sum_sq_inner_left]
  simp only [inner_gradient_left]
end StdBasis
end DifferentialTools
end
end
end
end
end

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
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
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section HessianSq
variable [FiniteDimensional ℝ E]
theorem FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis_apply (f : E → ℝ) (x : E) :
    hessianSqStdBasis f x = ∑ i, ∑ j,
      (bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)) ^ 2 :=
  rfl
end HessianSq
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
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
section Lp
section ScalarLp
omit [CompleteSpace E] [FiniteDimensional ℝ E]
section NormedSpace
variable {G : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
section CompleteSpace
variable [CompleteSpace G]
omit [BorelSpace E] in
/-- Tilt averages only see the `μ`-class of a function: every tilt `μ_z` is absolutely
continuous with respect to `μ`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.tiltAverage_congr_ae (μ : Measure E) {f g : E → G} (hfg : f =ᵐ[μ] g) (z : E) :
    tiltAverage μ f z = tiltAverage μ g z := by
  unfold tiltAverage expTilt
  exact integral_congr_ae ((tilted_absolutelyContinuous μ _).ae_le hfg)
omit [BorelSpace E] in
/-- Taylor tensors only see the `μ`-class of a function. -/
theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_congr_ae (μ : Measure E) {f g : E → G} (hfg : f =ᵐ[μ] g) (d : ℕ) :
    taylorTensor μ f d = taylorTensor μ g d := by
  unfold taylorTensor
  rw [show tiltAverage μ f = tiltAverage μ g from funext (tiltAverage_congr_ae μ hfg)]
end CompleteSpace
end NormedSpace
end ScalarLp
end Lp
end
end
end
end
end

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
/-- The zero constant is the zero element of `L²`. -/
@[simp]
theorem FunctionalInequalities.L2.const_zero (μ : ProbabilityMeasure α) : const μ 0 = 0 :=
  map_zero (Lp.const 2 (μ : Measure α))
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
/-- The mean of zero is zero. -/
@[simp]
theorem FunctionalInequalities.L2.mean_zero (μ : ProbabilityMeasure α) : mean μ 0 = 0 := by
  simp [mean]
/-- The mean preserves subtraction. -/
@[simp]
theorem FunctionalInequalities.L2.mean_sub (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f - g) = mean μ f - mean μ g := by
  rw [mean, inner_sub_left]
  rfl
/-- A centered `L²` element has mean zero. -/
@[simp]
theorem FunctionalInequalities.L2.mean_center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (center μ f) = 0 := by
  simp [center]
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
open MeasureTheory FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff LinearPMap RealInnerProductSpace
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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Generator
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
include hνU hU in
/-- **the smooth-test generator identity, value clause**: for `f ∈ C_c^∞(V)`, `T̄†T̄ [f] = [-ℒ f]` with `ℒ f = Δ f - ⟪∇U, ∇f⟫`.
The generator of the heat semigroup `P_t = exp (-t T̄†T̄)` is therefore `ℒ` on smooth compactly
supported tests: `d/dt P_t f |_{t=0} = ℒ f`. -/
theorem FunctionalInequalities.KLS.LogConcave.adjointComp_toLp_eq {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨(memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f,
          hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ =
      (memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).toLp (fun x => -weightedLaplacian U f x) := by
  rw [adjointComp_apply]
  refine LinearPMap.adjoint_apply_eq
    (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) _ fun x => ?_
  rw [hν.inner_toLp_neg_weightedLaplacian_eq m hi hνU hU hf hfc x]
  congr 1
  exact (hν.closedWeightedOperator_toLp_eq m hi hf hfc).symm
end Generator
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hν hi hνU hU in
/-- **Bakry–Gentil–Ledoux (2014), Corollary 4.8.2, in the heat-semigroup model**: if
`ν = m.tilted (-U)` is log-concave with full-dimensional support, `U` is `C²` and `∇∇U ≥ ρ > 0`,
then the literature Poincaré constant satisfies `C_P(ν) ≤ 1/ρ`. -/
theorem FunctionalInequalities.KLS.LogConcave.literatureConstant_le_inv {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal ρ⁻¹ := by
  exact literatureConstant_le_inv_of_tendsto_408915f m hν hi hνU hU hρ hH
    (fun u =>
      tendsto_norm_center_apply_408915f m hν hi hνU hU
        (u : Lp ℝ 2 (ν : Measure V)))
end
end
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace Classical
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
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.PoissonIterate
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ν : ProbabilityMeasure V} (T : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V))
omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- `normSq` is nonnegative. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_nonneg {k : ℕ} (u : Field ν k) : 0 ≤ normSq u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
end
end
end
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace
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
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.PoissonIterate
section General
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
variable {ν : ProbabilityMeasure V} (T : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V))
/-- The total gradient agrees with `T` on its domain. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_of_mem {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ T.domain) :
    weakGrad T u = T ⟨u, hu⟩ :=
  dif_pos hu
/-- The total generator agrees with `T†T` on its domain. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_of_mem {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain) :
    gen T u = adjointComp T ⟨u, hu⟩ :=
  dif_pos hu
/-- The total gradient of `0` is `0`. -/
@[simp]
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_zero : weakGrad T 0 = 0 := by
  rw [weakGrad_of_mem T T.domain.zero_mem]
  exact LinearPMap.map_zero T
/-- The total generator of `0` is `0`. -/
@[simp]
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_zero : gen T 0 = 0 := by
  rw [gen_of_mem T (adjointComp T).domain.zero_mem]
  exact LinearPMap.map_zero (adjointComp T)
/-- The total gradient is homogeneous, on and off the domain of `T`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_smul (c : ℝ) (u : Lp ℝ 2 (ν : Measure V)) :
    weakGrad T (c • u) = c • weakGrad T u := by
  by_cases hu : u ∈ T.domain
  · rw [weakGrad_of_mem T (T.domain.smul_mem c hu), weakGrad_of_mem T hu]
    exact LinearPMap.map_smul T c ⟨u, hu⟩
  · by_cases hc : c = 0
    · subst hc
      simp
    · have hcu : c • u ∉ T.domain := fun h => hu (by
        simpa [smul_smul, hc] using T.domain.smul_mem c⁻¹ h)
      simp [weakGrad, hu, hcu]
/-- The total generator is homogeneous on the domain of `T†T`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_smul (c : ℝ) {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain) :
    gen T (c • u) = c • gen T u := by
  rw [gen_of_mem T ((adjointComp T).domain.smul_mem c hu), gen_of_mem T hu]
  exact LinearPMap.map_smul (adjointComp T) c ⟨u, hu⟩
/-- The centered inverse is always centered (it is `0` when no centered preimage exists). -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.mean_centeredInv (g : Lp ℝ 2 (ν : Measure V)) : L2.mean ν (centeredInv T g) = 0 := by
  unfold centeredInv
  split_ifs with h
  · exact h.choose_spec.1
  · exact L2.mean_zero ν
/-- If a centered preimage of `g` under `T†T` exists, the centered inverse is one. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_spec_of_exists {g : Lp ℝ 2 (ν : Measure V)}
    (h : ∃ u : (adjointComp T).domain,
      L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0 ∧ adjointComp T u = g) :
    ∃ hu : centeredInv T g ∈ (adjointComp T).domain, adjointComp T ⟨_, hu⟩ = g := by
  have hc : centeredInv T g = (h.choose : Lp ℝ 2 (ν : Measure V)) := by
    unfold centeredInv
    rw [dif_pos h]
  rw [hc]
  exact ⟨h.choose.2, h.choose_spec.2⟩
/-- `normSq` is quadratic: `‖c u‖² = c² ‖u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_smul {k : ℕ} (c : ℝ) (u : Field ν k) : normSq (c • u) = c ^ 2 * normSq u := by
  unfold normSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
/-- `normSq u = 0` exactly when every component vanishes. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_eq_zero_iff {k : ℕ} (u : Field ν k) : normSq u = 0 ↔ ∀ I, u I = 0 := by
  unfold normSq
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _]
  simp
variable [FiniteDimensional ℝ V]
/-- Parseval for the weak partial derivatives: `Σ_j ‖∂_j u‖² = ‖∇u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_norm_sq_partialDeriv (u : Lp ℝ 2 (ν : Measure V)) :
    ∑ j, ‖partialDeriv T j u‖ ^ 2 = ‖weakGrad T u‖ ^ 2 :=
  L2.sum_norm_sq_compLp_innerSL_408915f (stdOrthonormalBasis ℝ V) (weakGrad T u)
/-- The energy of a field is the sum of the squared gradient norms of its components. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_eq_sum {k : ℕ} (u : Field ν k) :
    energy T u = ∑ I, ‖weakGrad T (u I)‖ ^ 2 := by
  unfold energy normSq gradField
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin (Module.finrank ℝ V)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [Fin.consEquiv_apply, Fin.cons_zero]
  exact sum_norm_sq_partialDeriv T (u I)
/-- The energy is nonnegative. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_nonneg {k : ℕ} (u : Field ν k) : 0 ≤ energy T u :=
  normSq_nonneg _
/-- The energy is quadratic: `‖∇(c u)‖² = c² ‖∇u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_smul {k : ℕ} (c : ℝ) (u : Field ν k) : energy T (c • u) = c ^ 2 * energy T u := by
  rw [energy_eq_sum, energy_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Pi.smul_apply, weakGrad_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
omit [FiniteDimensional ℝ V] in
/-- Centering the components removes the squared means: `‖u‖² - ‖u - ∫u‖² = Σ_J (∫u_J)²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_sub_normSq_center {k : ℕ} (u : Field ν k) :
    normSq u - normSq (fun J => L2.center ν (u J)) = ∑ J, L2.mean ν (u J) ^ 2 := by
  unfold normSq
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  have h := L2.inner_center_center_408915f ν (u J) (u J)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [h]
  ring
/-- The energy drop of BKL (35) in the form `‖∇h‖² - ‖∇₀h‖² = |∫∇h|²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_sub_normSq_grad0 {k : ℕ} (h : Field ν k) :
    energy T h - normSq (grad0 T h) = meanGradSq T h :=
  normSq_sub_normSq_center (gradField T h)
/-- The components of `∇₀h` are centered. -/
@[simp]
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.mean_grad0 {k : ℕ} (h : Field ν k) (J : Fin (k + 1) → Fin (Module.finrank ℝ V)) :
    L2.mean ν (grad0 T h J) = 0 :=
  L2.mean_center ν _
/-- The iterates satisfy the recursion (30) definitionally. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter_succ (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ) :
    iter T f (k + 1) = step T (iter T f k) :=
  rfl
/-- The iterate `h₁` is `f`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter_zero (f : Lp ℝ 2 (ν : Measure V)) (I : Fin 0 → Fin (Module.finrank ℝ V)) :
    iter T f 0 I = f :=
  rfl
end General
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
include hC in
/-- The Poincaré gap for a centered `u ∈ D(T̄)`: `‖u‖² ≤ C ‖∇u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_sq_le_weakGrad {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (T̄).domain)
    (hmean : L2.mean ν u = 0) : ‖u‖ ^ 2 ≤ (C : ℝ) * ‖weakGrad T̄ u‖ ^ 2 := by
  have h := hν.closedWeightedOperator_id_gap_of_literature_le_408915f m hi C hC ⟨u, hu⟩
  have hcenter : L2.center ν u = u := by simp [L2.center, hmean]
  rw [weakGrad_of_mem _ hu]
  simpa [hcenter] using h
include hνU hU hC in
/-- **BKL Lemma 2.1 for the total centered inverse.** For centered `g`, `centeredInv T̄ g` lies in
`D(A)` and solves `A u = g`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_spec {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    ∃ hu : centeredInv T̄ g ∈ (adjointComp T̄).domain, adjointComp T̄ ⟨_, hu⟩ = g :=
  centeredInv_spec_of_exists _
    (existsUnique_centered_adjointComp_eq_408915f m hν hi hνU hU hC g hg).exists
include hνU hU hC in
/-- For centered `g`, `(-L)⁻¹ g ∈ D(A)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_mem_domain {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    centeredInv T̄ g ∈ (adjointComp T̄).domain :=
  (centeredInv_spec m hν hi hνU hU hC hg).1
include hνU hU hC in
/-- For centered `g`, `-L (-L)⁻¹ g = g`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_centeredInv {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    gen T̄ (centeredInv T̄ g) = g := by
  obtain ⟨hu, hAu⟩ := centeredInv_spec m hν hi hνU hU hC hg
  rw [gen_of_mem _ hu, hAu]
include hνU hU hC in
/-- The components of one step lie in `D(A)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.step_mem_domain {k : ℕ} (h : Field ν k) (J : Fin (k + 1) → Fin (Module.finrank ℝ V)) :
    step T̄ h J ∈ (adjointComp T̄).domain :=
  (adjointComp T̄).domain.smul_mem _
    (centeredInv_mem_domain m hν hi hνU hU hC (mean_grad0 (T̄) h J))
include hνU hU hC in
/-- **BKL (30)** for one step: `-L (α (-L)⁻¹ ∇₀h) = α ∇₀h`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.genField_step {k : ℕ} (h : Field ν k) :
    genField T̄ (step T̄ h) = scale T̄ h • grad0 T̄ h := by
  funext J
  rw [genField, step, Pi.smul_apply, Pi.smul_apply, invField,
    gen_smul _ _ (centeredInv_mem_domain m hν hi hνU hU hC (mean_grad0 (T̄) h J)),
    gen_centeredInv m hν hi hνU hU hC (mean_grad0 (T̄) h J)]
include hνU hU hC in
/-- If `∇(-L)⁻¹∇₀h = 0` then `∇₀h = 0`: the centered `w_J` with `∇w_J = 0` vanish by the Poincaré
gap, so `∇₀h_J = A w_J = 0`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_eq_zero_of_energy_eq_zero {k : ℕ} (h : Field ν k)
    (h0 : energy T̄ (invField T̄ (grad0 T̄ h)) = 0) : normSq (grad0 T̄ h) = 0 := by
  rw [normSq_eq_zero_iff]
  intro J
  have hJ : ‖weakGrad T̄ (invField T̄ (grad0 T̄ h) J)‖ ^ 2 = 0 := by
    rw [energy_eq_sum, Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at h0
    exact h0 J (Finset.mem_univ J)
  have hmem := centeredInv_mem_domain m hν hi hνU hU hC (mean_grad0 (T̄) h J)
  have hgap := norm_sq_le_weakGrad m hν hi hC hmem.2 (mean_centeredInv (T̄) _)
  rw [invField] at hJ
  rw [hJ, mul_zero] at hgap
  have hw : centeredInv T̄ (grad0 T̄ h J) = 0 := by
    have hn := norm_nonneg (centeredInv T̄ (grad0 T̄ h J))
    have : ‖centeredInv T̄ (grad0 T̄ h J)‖ = 0 := by nlinarith
    exact norm_eq_zero.mp this
  rw [← gen_centeredInv m hν hi hνU hU hC (mean_grad0 (T̄) h J), hw, gen_zero]
include hνU hU hC in
/-- **BKL (33)** for one step: `‖∇(α (-L)⁻¹∇₀h)‖² = ‖∇₀h‖²`, also when `∇₀h = 0`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_step {k : ℕ} (h : Field ν k) :
    energy T̄ (step T̄ h) = normSq (grad0 T̄ h) := by
  rw [step, energy_smul]
  by_cases h0 : energy T̄ (invField T̄ (grad0 T̄ h)) = 0
  · rw [h0, mul_zero, normSq_grad0_eq_zero_of_energy_eq_zero m hν hi hνU hU hC h h0]
  · have hs : scale T̄ h = Real.sqrt (normSq (grad0 T̄ h) /
        energy T̄ (invField T̄ (grad0 T̄ h))) := if_neg h0
    rw [hs, Real.sq_sqrt (div_nonneg (normSq_nonneg _) (energy_nonneg _ _)),
      div_mul_cancel₀ _ h0]
include hνU hU hC in
/-- **BKL (46)** for one step: `‖L h'‖² = α² ‖∇h'‖²` for `h' = α (-L)⁻¹∇₀h`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_genField_step {k : ℕ} (h : Field ν k) :
    normSq (genField T̄ (step T̄ h)) = scale T̄ h ^ 2 * energy T̄ (step T̄ h) := by
  rw [genField_step m hν hi hνU hU hC, normSq_smul, energy_step m hν hi hνU hU hC]
include hνU hU hC in
/-- **BKL (35)** for one step: `‖∇h‖² - ‖∇h'‖² = |∫∇h|²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_sub_energy_step {k : ℕ} (h : Field ν k) :
    energy T̄ h - energy T̄ (step T̄ h) = meanGradSq T̄ h := by
  rw [energy_step m hν hi hνU hU hC, energy_sub_normSq_grad0]
include hνU hU hC in
/-- **The iterates lie in `D(A)`.** Every component of `h_{k+1} = iter T̄ f k` lies in `D(A)`, for
`f ∈ D(A)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter_mem_adjointComp_domain {f : Lp ℝ 2 (ν : Measure V)}
    (hf : f ∈ (adjointComp T̄).domain) (k : ℕ) (I : Fin k → Fin (Module.finrank ℝ V)) :
    iter T̄ f k I ∈ (adjointComp T̄).domain := by
  cases k with
  | zero => exact hf
  | succ k => exact step_mem_domain m hν hi hνU hU hC _ I
include hνU hU hC in
/-- **BKL (33).** `‖∇h_{k+2}‖² = ‖∇₀h_{k+1}‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_iter_succ (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ) :
    energy T̄ (iter T̄ f (k + 1)) = normSq (grad0 T̄ (iter T̄ f k)) :=
  energy_step m hν hi hνU hU hC _
include hνU hU hC in
/-- **BKL (46).** `‖L h_{k+2}‖² = α_{k+2}² ‖∇h_{k+2}‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_genField_iter_succ (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ) :
    normSq (genField T̄ (iter T̄ f (k + 1))) =
      scale T̄ (iter T̄ f k) ^ 2 * energy T̄ (iter T̄ f (k + 1)) :=
  normSq_genField_step m hν hi hνU hU hC _
include hνU hU hC in
/-- **BKL (35).** `v_{k+1} - v_{k+2} = p_{k+1}`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_sub_energy_iter_succ (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ) :
    energy T̄ (iter T̄ f k) - energy T̄ (iter T̄ f (k + 1)) = meanGradSq T̄ (iter T̄ f k) :=
  energy_sub_energy_step m hν hi hνU hU hC _
include hνU hU hC in
/-- **BKL (32).** If `α_{k+2} > 0` then `α_{k+2}² ≥ 1/C`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.inv_le_scale_sq (hCpos : 0 < C) (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ)
    (hs : 0 < scale T̄ (iter T̄ f k)) : (C : ℝ)⁻¹ ≤ scale T̄ (iter T̄ f k) ^ 2 :=
  inv_le_scale_sq_step_408915f m hν hi hνU hU hC hCpos _ hs
include hνU hU hC in
/-- **BKL (36).** `v₁ = v_{N+1} + Σ_{k<N} p_{k+1}`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_iter_zero_eq (f : Lp ℝ 2 (ν : Measure V)) (N : ℕ) :
    energy T̄ (iter T̄ f 0) =
      energy T̄ (iter T̄ f N) + ∑ k ∈ Finset.range N, meanGradSq T̄ (iter T̄ f k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ,
      ← energy_sub_energy_iter_succ m hν hi hνU hU hC f N]
    ring
end HeatModel
end
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
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
open Energy Energy.WeightedGradient
section Partial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [CompleteSpace V] [FiniteDimensional ℝ V]
/-- `Σᵢ ‖∇ (∂ᵢ f)(x)‖² = Σᵢ Σⱼ (∇²f(x)(eᵢ, eⱼ))²` in the standard orthonormal basis. -/
private theorem FunctionalInequalities.KLS.LogConcave.sum_norm_gradient_fderiv_apply_sq {f : V → ℝ} (hf : ContDiff ℝ 2 f) (x : V) :
    ∑ i, ‖gradient (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ V i)) x‖ ^ 2 =
      hessianSqStdBasis f x := by
  rw [hessianSqStdBasis_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_gradient_sq_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hf]
end Partial
section Hessian
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
/-- The smooth curvature inequality in `L²` norms: for `f ∈ C_c^∞` and `∇²U ≥ ρ`,
`Σᵢ ‖T̄ [∂ᵢ f]‖² + ρ ‖T̄ [f]‖² ≤ ‖A [f]‖²`. -/
private theorem FunctionalInequalities.KLS.LogConcave.sum_norm_sq_add_le_of_smooth (hνU : (ν : Measure V) = m.tilted (-U))
    (hUt : U.HasTemperateGrowth) (hU : ContDiff ℝ 1 U)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∑ i, ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
          (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf (stdOrthonormalBasis ℝ V i))
          (hfc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V i))⟩‖ ^ 2 +
      ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩‖ ^ 2 ≤
    ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩‖ ^ 2 := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hsum : ∑ i, ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
          (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf (stdOrthonormalBasis ℝ V i))
          (hfc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V i))⟩‖ ^ 2 =
      ∫ x, hessianSqStdBasis f x ∂(ν : Measure V) := by
    have hmem : ∀ i, MemLp (gradient (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ V i))) 2
        (ν : Measure V) := fun i =>
      memLp_gradient_of_contDiff_hasCompactSupport
        (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf _) (hfc.fderiv_apply ℝ _)
    calc _ = ∑ i, ∫ x, ‖gradient (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ V i)) x‖ ^ 2
          ∂(ν : Measure V) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hν.closedWeightedOperator_toLp_eq m hi (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf _)
            (hfc.fderiv_apply ℝ _), L2.norm_toLp_sq]
      _ = ∫ x, ∑ i, ‖gradient (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ V i)) x‖ ^ 2
          ∂(ν : Measure V) :=
          (integral_finsetSum _ fun i _ =>
            (memLp_two_iff_integrable_sq_norm (hmem i).1).1 (hmem i)).symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun x =>
          sum_norm_gradient_fderiv_apply_sq hf2 x)
  rw [hsum, hν.closedWeightedOperator_toLp_eq m hi hf hfc,
    hν.adjointComp_toLp_eq m hi hνU hU hf hfc, L2.norm_toLp_sq, L2.norm_toLp_sq]
  simp only [norm_neg, Real.norm_eq_abs, sq_abs]
  have hexp' : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-U)) :=
    hνU ▸ hexp
  rw [hνU]
  have h := integral_hessianSq_add_le_of_hasTemperateGrowth_408915f m hUt hexp'
    (hfc.hasTemperateGrowth hf) hH
  simpa only [Real.norm_eq_abs, sq_abs] using h
omit [CompleteSpace V] in
include hν in
/-- The curvature bound `∇²U ≥ 0` of a log-concave tilted law with a `C²` potential. -/
private theorem FunctionalInequalities.KLS.LogConcave.zero_mul_le_bilinearIteratedFDerivTwo (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 2 U) (x v : V) :
    0 * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v := by
  rw [zero_mul]
  exact bilinearIteratedFDerivTwo_nonneg_of_convexOn hU
    (convexOn_of_eq_tilted_408915f m hν hνU hU.continuous) x v
/-- **the weak Hessian estimate, weak first derivatives in the form domain.** For `ν = m.tilted (-U)` log-concave,
with `U` of temperate growth and all exponential moments, and `F ∈ D(A)`, every weak first
derivative `∂ᵢ F = ⟪eᵢ, T̄ F⟫` (standard orthonormal basis) lies in `D(T̄)`. No curvature bound
beyond the convexity of `U` implied by log-concavity is assumed. -/
theorem FunctionalInequalities.KLS.LogConcave.compLp_innerSL_mem_closedWeightedOperator_domain
    (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (i : Fin (Module.finrank ℝ V)) :
    (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := by
  have hU2 : ContDiff ℝ 2 U := hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨_, _, _, -, -, hD⟩ := exists_seq_smooth_tendsto_weakHessian_408915f m hν hi hνU hUt
    (hU2.of_le (by norm_num)) hexp (zero_mul_le_bilinearIteratedFDerivTwo m hν hνU hU2) F
  exact (hD i).1
/-- **the weak Hessian estimate, the curvature form of BKL (16) on `D(A)`.** Under the hypotheses of
`compLp_innerSL_mem_closedWeightedOperator_domain`, if `∇²U ≥ ρ` for a real `ρ`, then
`Σᵢ ‖T̄ ∂ᵢ F‖² + ρ ‖T̄ F‖² ≤ ‖A F‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.sum_norm_sq_closedWeightedOperator_add_le
    (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hD : ∀ i, (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    ∑ i, ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD i⟩‖ ^ 2 +
        ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩‖ ^ 2 ≤
      ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F‖ ^ 2 := by
  have hU1 : ContDiff ℝ 1 U := hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨fn, hfn, hfnc, hTF, hAF, hlim⟩ :=
    exists_seq_smooth_tendsto_weakHessian_408915f m hν hi hνU hUt hU1 hexp hH F
  have hL := (tendsto_finsetSum Finset.univ fun i _ => ((hlim i).2.norm.pow 2)).add
    ((hTF.norm.pow 2).const_mul ρ)
  exact le_of_tendsto_of_tendsto' hL (hAF.norm.pow 2) fun n =>
    sum_norm_sq_add_le_of_smooth m hν hi hνU hUt hU1 hexp hH (hfn n) (hfnc n)
end Hessian
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
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
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
variable (m : Measure E) [m.IsAddHaarMeasure]
/-- Telescoping (45): `L₀ ≥ L_N + ∑_{i<N} χ_i + a ∑_{i<N} v_i`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.telescope_energy {L χ v : ℕ → ℝ} {a : ℝ}
    (h45 : ∀ i, L (i + 1) + χ i + a * v i ≤ L i) (N : ℕ) :
    L N + ∑ i ∈ Finset.range N, χ i + a * ∑ i ∈ Finset.range N, v i ≤ L 0 := by
    induction N with
    | zero =>
        simp
    | succ N ih =>
        simp only [Finset.sum_range_succ]
        linarith [h45 N]
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace
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
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.PoissonIterate
section General
/-- Splitting off the first index position: `Σ_{J'} F J' = Σ_J Σ_j F (j, J)`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_cons {n k : ℕ} {M : Type*} [AddCommMonoid M]
    (F : (Fin (k + 1) → Fin n) → M) :
    ∑ J, F J = ∑ J, ∑ j, F (Fin.cons j J) := by
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin n).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl
variable {α : Type*} [MeasurableSpace α] {ν : ProbabilityMeasure α}
end General
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
  {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- A potential of temperate growth is `C²`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.contDiff_two (hUt : U.HasTemperateGrowth) : ContDiff ℝ 2 U :=
  hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
/-- A weak partial derivative on `D(T̄)` in terms of `T̄`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv_eq {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (T̄).domain)
    (j : Fin (Module.finrank ℝ V)) :
    partialDeriv T̄ j u = (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp (T̄ ⟨u, hu⟩) := by
  rw [partialDeriv, weakGrad_of_mem _ hu]
include hνU hUt hexp in
/-- The curvature form of BKL (16) on `D(A)` in terms of the total operators:
`Σ_j ‖∇∂_j u‖² + a ‖∇u‖² ≤ ‖L u‖²` for `u ∈ D(A)` when `∇²U ≥ a`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_norm_sq_weakGrad_partialDeriv_add_le {a : ℝ}
    (ha : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T̄).domain) :
    ∑ j, ‖weakGrad T̄ (partialDeriv T̄ j u)‖ ^ 2 + a * ‖weakGrad T̄ u‖ ^ 2 ≤ ‖gen T̄ u‖ ^ 2 := by
  have hD : ∀ l, (innerSL ℝ (stdOrthonormalBasis ℝ V l)).compLp (T̄ ⟨u, hu.2⟩) ∈ (T̄).domain :=
    compLp_innerSL_mem_closedWeightedOperator_domain m hν hi hνU hUt hexp ⟨u, hu⟩
  have h := sum_norm_sq_closedWeightedOperator_add_le m hν hi hνU hUt hexp ha ⟨u, hu⟩ hD
  have e : ∀ j, weakGrad T̄ (partialDeriv T̄ j u) = T̄ ⟨_, hD j⟩ := fun j => by
    rw [partialDeriv_eq m hν hi hu.2, weakGrad_of_mem _ (hD j)]
  simp only [e]
  rw [weakGrad_of_mem _ hu.2, gen_of_mem _ hu]
  exact h
include hνU hUt hexp hC in
/-- **BKL Lemma 3.4 for one step.** For a field `h` with components in `D(A)`, `∇²U ≥ a` and
`h' = α (-L)⁻¹ ∇₀h`: `‖L h'‖² + χ + a ‖∇h‖² ≤ ‖L h‖²`, with `χ = ‖∇²h - α ∇h'‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_genField_step_add_defect_le {a : ℝ}
    (ha : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) {k : ℕ} (h : Field ν k)
    (hh : ∀ I, h I ∈ (adjointComp T̄).domain) :
    normSq (genField T̄ (step T̄ h)) + defect T̄ h + a * energy T̄ h ≤ normSq (genField T̄ h) := by
  rw [← normSq_gradField_gradField_step_408915f m hν hi hνU hUt hexp hC h hh]
  have hH : normSq (gradField T̄ (gradField T̄ h)) =
      ∑ I, ∑ j, ‖weakGrad T̄ (partialDeriv T̄ j (h I))‖ ^ 2 := by
    rw [show normSq (gradField T̄ (gradField T̄ h)) = energy T̄ (gradField T̄ h) from rfl,
      energy_eq_sum, sum_cons]
    rfl
  rw [hH, energy_eq_sum, normSq, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun I _ =>
    sum_norm_sq_weakGrad_partialDeriv_add_le m hν hi hνU hUt hexp ha (hh I)
include hνU hUt hexp hC in
/-- **BKL Lemma 3.4.** For `f ∈ D(A)` and `∇²U ≥ a`:
`‖L h_{k+2}‖² + χ_{k+1} + a ‖∇h_{k+1}‖² ≤ ‖L h_{k+1}‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_genField_iter_succ_add_defect_le {a : ℝ}
    (ha : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) (k : ℕ) :
    normSq (genField T̄ (iter T̄ f (k + 1))) + defect T̄ (iter T̄ f k) +
        a * energy T̄ (iter T̄ f k) ≤ normSq (genField T̄ (iter T̄ f k)) :=
  normSq_genField_step_add_defect_le m hν hi hνU hUt hexp hC ha _
    (iter_mem_adjointComp_domain m hν hi hνU (contDiff_two hUt) hC hf k)
include hνU hUt hexp hC in
/-- **BKL Corollary 3.5.** For `f ∈ D(A)` and `∇²U ≥ a > 0`, the energies `‖∇h_{k+1}‖²` are
summable and tend to `0`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.tendsto_energy_iter_zero {a : ℝ} (ha₀ : 0 < a)
    (ha : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) :
    Tendsto (fun k => energy T̄ (iter T̄ f k)) atTop (𝓝 0) :=
  (Analysis.BakryEmery.summable_and_tendsto_zero_of_energy_408915f
    (L := fun k => normSq (genField T̄ (iter T̄ f k))) (χ := fun k => defect T̄ (iter T̄ f k))
    (v := fun k => energy T̄ (iter T̄ f k)) ha₀ (fun _ => normSq_nonneg _)
    (fun _ => normSq_nonneg _) (fun _ => energy_nonneg _ _)
    (normSq_genField_iter_succ_add_defect_le m hν hi hνU hUt hexp hC ha hf)).2.2
include hνU hUt hexp hC in
/-- **The summed defects.** For `f ∈ D(A)` and `∇²U ≥ a ≥ 0`:
`Σ_{k<N} χ_{k+1} ≤ ‖L f‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_defect_iter_le {a : ℝ} (ha₀ : 0 ≤ a)
    (ha : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) (N : ℕ) :
    ∑ k ∈ Finset.range N, defect T̄ (iter T̄ f k) ≤ normSq (genField T̄ (iter T̄ f 0)) := by
  have h := Analysis.BakryEmery.telescope_energy
    (L := fun k => normSq (genField T̄ (iter T̄ f k))) (χ := fun k => defect T̄ (iter T̄ f k))
    (v := fun k => energy T̄ (iter T̄ f k))
    (normSq_genField_iter_succ_add_defect_le m hν hi hνU hUt hexp hC ha hf) N
  have hv : 0 ≤ a * ∑ k ∈ Finset.range N, energy T̄ (iter T̄ f k) :=
    mul_nonneg ha₀ (Finset.sum_nonneg fun _ _ => energy_nonneg _ _)
  linarith [normSq_nonneg (genField T̄ (iter T̄ f N))]
end HeatModel
end
end
end
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
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
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.PoissonIterate
section Generic
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : ProbabilityMeasure V}
omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- `T_d` is homogeneous on `L²(ν)` classes. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_Lp_smul (c : ℝ) (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ) :
    taylorTensor (ν : Measure V) (⇑(c • u)) d = c • taylorTensor (ν : Measure V) (⇑u) d := by
  rw [taylorTensor_congr_ae _ (Lp.coeFn_smul c u) d]
  exact taylorTensor_const_mul_408915f _ c _ d
omit [BorelSpace V] in
/-- `taylorField d` is homogeneous. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField_smul (d : ℕ) {k : ℕ} (c : ℝ) (u : Field ν k) :
    taylorField d (c • u) = c • taylorField d u := by
  ext J
  simp only [taylorField, Pi.smul_apply, taylorTensor_Lp_smul, PiLp.toLp_apply, PiLp.smul_apply,
    smul_apply, smul_eq_mul]
end Generic
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
variable {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
include hνU hU hexp hC in
/-- **BKL (61)** for one step: `|∫ ∇h'|² = α² |T₁(∇₀h)|²` for `h' = α (-L)⁻¹∇₀h`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.meanGradSq_step {k : ℕ} (h : Field ν k) :
    meanGradSq T̄ (step T̄ h) = scale T̄ h ^ 2 * ‖taylorField 1 (grad0 T̄ h)‖ ^ 2 := by
  rw [meanGradSq_eq_norm_taylorField_one_genField_408915f m hν hi hνU hU hexp _
      (step_mem_domain m hν hi hνU hU hC h), genField_step m hν hi hνU hU hC, taylorField_smul,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
include hexp in
/-- The first term of BKL Lemma 3.9: `p₁ ≤ ‖L h₁‖²` for `h₁ = f ∈ D(A)` and `Cov ν ≤ Id`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.meanGradSq_iter_zero_le
    (hcov : ∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) :
    meanGradSq T̄ (iter T̄ f 0) ≤ normSq (genField T̄ (iter T̄ f 0)) := by
  have h1 : meanGradSq T̄ (iter T̄ f 0) = ∑ j, L2.mean ν (partialDeriv T̄ j f) ^ 2 :=
    Fintype.sum_equiv (Equiv.funUnique (Fin 1) _) _ _ fun K => rfl
  have h2 : normSq (genField T̄ (iter T̄ f 0)) = ‖gen T̄ f‖ ^ 2 := by
    simp [normSq, genField, iter]
  rw [h1, h2]
  exact sum_mean_partialDeriv_sq_le_408915f m hν hi hexp hcov hf
include hνU hU hexp hC in
/-- **BKL Lemma 3.9 in the route form**: if `∫ ⟪v, x⟫² dν ≤ ‖v‖²` for every `v` and
`α_{j+2}² ≤ β/C` for `j + 1 < N`, then
`Σ_{k<N} p_{k+1} ≤ ‖L h₁‖² + (β/C) Σ_{k<N-1} |T₁(∇₀h_{k+1})|²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_meanGradSq_iter_le
    (hcov : ∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) {β : ℝ} (N : ℕ)
    (hβ : ∀ j, j + 1 < N → scale T̄ (iter T̄ f j) ^ 2 ≤ β / C) :
    ∑ k ∈ Finset.range N, meanGradSq T̄ (iter T̄ f k) ≤
      normSq (genField T̄ (iter T̄ f 0)) +
        β / C * ∑ k ∈ Finset.range (N - 1), ‖taylorField 1 (grad0 T̄ (iter T̄ f k))‖ ^ 2 := by
  cases N with
  | zero => simpa using normSq_nonneg _
  | succ M =>
    rw [Finset.sum_range_succ', Nat.add_sub_cancel, Finset.mul_sum, add_comm]
    refine add_le_add (meanGradSq_iter_zero_le m hν hi hexp hcov hf)
      (Finset.sum_le_sum fun k hk => ?_)
    rw [iter_succ, meanGradSq_step m hν hi hνU hU hexp hC]
    exact mul_le_mul_of_nonneg_right (hβ k (by simp at hk; omega)) (sq_nonneg _)
end HeatModel
end
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff
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
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.PoissonIterate
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
/-- The scale `α` is nonnegative, and `α_k = 0` forces `v_{k+1} = 0`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale_nonneg_and_energy (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ) :
    0 ≤ scale T̄ (iter T̄ f k) ∧
      (scale T̄ (iter T̄ f k) = 0 → energy T̄ (iter T̄ f (k + 1)) = 0) := by
  refine ⟨?_, fun h0 => ?_⟩
  · unfold scale
    split_ifs
    · exact le_rfl
    · exact Real.sqrt_nonneg _
  · rw [iter_succ, step, energy_smul, h0]
    ring
/-- The initial data of the iterates from an approximate eigenfunction `‖A f - λ f‖ ≤ λ/10`,
`λ = 1/C`, centered and of norm one: `v₀ = ‖∇f‖² ≥ λ` (the Poincaré gap) and
`‖L h₁‖² = ‖A f‖² ≤ (1.1 λ)²`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.initial_bounds {C : NNReal}
    (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    (f : (adjointComp T̄).domain) (hfm : L2.mean ν (f : Lp ℝ 2 (ν : Measure V)) = 0)
    (hfn : ‖(f : Lp ℝ 2 (ν : Measure V))‖ = 1)
    (hfA : ‖adjointComp T̄ f - (C : ℝ)⁻¹ • (f : Lp ℝ 2 (ν : Measure V))‖ ≤
      (C : ℝ)⁻¹ * (1 / 10)) :
    (C : ℝ)⁻¹ ≤ energy T̄ (iter T̄ (f : Lp ℝ 2 (ν : Measure V)) 0) ∧
      normSq (genField T̄ (iter T̄ (f : Lp ℝ 2 (ν : Measure V)) 0)) ≤
        (11 / 10 * (C : ℝ)⁻¹) ^ 2 := by
  have hC0 : (0 : ℝ) ≤ (C : ℝ)⁻¹ := inv_nonneg.mpr (NNReal.coe_nonneg C)
  constructor
  · rw [energy_eq_sum, Fintype.sum_unique, iter_zero]
    have hgap := norm_sq_le_weakGrad m hν hi hC f.2.2 hfm
    rw [hfn, one_pow] at hgap
    rcases (NNReal.coe_nonneg C).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul] at hgap
      norm_num at hgap
    · calc (C : ℝ)⁻¹ = (C : ℝ)⁻¹ * 1 := (mul_one _).symm
        _ ≤ (C : ℝ)⁻¹ * ((C : ℝ) * ‖weakGrad T̄ (f : Lp ℝ 2 (ν : Measure V))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hgap hC0
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  · rw [normSq, Fintype.sum_unique, genField, iter_zero, gen_of_mem _ f.2, Subtype.coe_eta]
    have h1 : ‖adjointComp T̄ f‖ ≤ 11 / 10 * (C : ℝ)⁻¹ := by
      calc ‖adjointComp T̄ f‖ ≤ ‖adjointComp T̄ f - (C : ℝ)⁻¹ • (f : Lp ℝ 2 (ν : Measure V))‖ +
            ‖(C : ℝ)⁻¹ • (f : Lp ℝ 2 (ν : Measure V))‖ := norm_le_norm_sub_add _ _
        _ ≤ (C : ℝ)⁻¹ * (1 / 10) + (C : ℝ)⁻¹ := by
          rw [norm_smul, hfn, mul_one, Real.norm_of_nonneg hC0]
          linarith
        _ = 11 / 10 * (C : ℝ)⁻¹ := by ring
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
include hν hi in
/-- The core of the criterion: if `C_P(ν) = C > 0`, then `C ≤ K R²`, by running the iterates of
an approximate eigenfunction (`exists_centered_approx_eigenfunction`, `η = 1/10`) through
`le_of_iterate_bounds`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.coe_le_of_eq
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : U.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    {a : ℝ} (ha : 0 < a) (hUa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (hcov : ∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2)
    {R : ℝ} (hR : 1 ≤ R)
    (h29 : ∀ (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ), 1 ≤ d →
      ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑u) d)‖ ≤
        R ^ d * ‖u‖)
    {C : NNReal} (hCpos : 0 < C) (hCP : Poincare.LocalSlope.Intrinsic.constant ν = (C : ENNReal)) :
    (C : ℝ) ≤ taylorCriterionConstant * R ^ 2 := by
  have hU2 : ContDiff ℝ 2 U := hU.1.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨f, hfm, hfn, hfA⟩ := exists_centered_approx_eigenfunction_408915f m hν hi hνU hU2 hCpos hCP
    (η := 1 / 10) (by norm_num)
  have hCle := hCP.le
  have hF : (f : Lp ℝ 2 (ν : Measure V)) ∈ (adjointComp T̄).domain := f.2
  obtain ⟨hv0, hL0⟩ := initial_bounds m hν hi hCle f hfm hfn hfA
  have hc : (1 : ℝ) ≤ 2 ^ 20 * max 1 3 ^ 2 := by norm_num
  have key := le_of_iterate_bounds_408915f
    (v := fun k => energy T̄ (iter T̄ (f : Lp ℝ 2 (ν : Measure V)) k))
    (p := fun k => meanGradSq T̄ (iter T̄ (f : Lp ℝ 2 (ν : Measure V)) k))
    (χ := fun k => defect T̄ (iter T̄ (f : Lp ℝ 2 (ν : Measure V)) k))
    (L := fun k => normSq (genField T̄ (iter T̄ (f : Lp ℝ 2 (ν : Measure V)) k)))
    (α := fun k => scale T̄ (iter T̄ (f : Lp ℝ 2 (ν : Measure V)) k))
    (t := fun d k => ‖taylorField d (grad0 T̄ (iter T̄ (f : Lp ℝ 2 (ν : Measure V)) k))‖ ^ 2)
    (NNReal.coe_pos.mpr hCpos) hc hR (fun k => energy_nonneg _ _) hv0
    (tendsto_energy_iter_zero m hν hi hνU hU hexp hCle ha hUa hF)
    (energy_iter_zero_eq m hν hi hνU hU2 hCle _) (fun k => normSq_nonneg _)
    (sum_defect_iter_le m hν hi hνU hU hexp hCle ha.le hUa hF) hL0
    (fun k => by
      have h5 := normSq_genField_iter_succ_add_defect_le m hν hi hνU hU hexp hCle hUa hF k
      have h6 : 0 ≤ defect T̄ (iter T̄ (f : Lp ℝ 2 (ν : Measure V)) k) := normSq_nonneg _
      have h7 := mul_nonneg ha.le (energy_nonneg (T̄) (iter T̄ (f : Lp ℝ 2 (ν : Measure V)) k))
      linarith)
    (normSq_genField_iter_succ m hν hi hνU hU2 hCle _)
    (fun k => (scale_nonneg_and_energy m hν hi _ k).1)
    (fun k => (scale_nonneg_and_energy m hν hi _ k).2)
    (fun k hs => inv_le_scale_sq m hν hi hνU hU2 hCle hCpos _ k hs)
    (fun d k => sq_nonneg _)
    (fun d k hd => by
      rw [energy_iter_succ m hν hi hνU hU2 hCle]
      exact norm_taylorField_sq_le_408915f (fun g => h29 g d hd) _)
    (fun k d hd hdk hα => norm_taylorField_grad0_iter_sq_le_408915f m hν hi hνU hU hexp hCle hCpos h29 hF
      (β := 3) k d hd hdk hα)
    (fun N hN => sum_meanGradSq_iter_le m hν hi hνU hU2 hexp hCle hcov hF (β := 3) N hN)
  rw [taylorCriterionConstant]
  linarith
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities.KLS.LogConcave.PoissonIterate in
include hν hi in
/-- **BKL Theorem 3.1 in the heat model** (arXiv:2610.05474v1, p. 10, proof p. 17, in the
operator route). Let `ν = m.tilted (-U)` with `U` of temperate growth, all exponential moments,
`∇²U ≥ a > 0` and `∫ ⟪v, x⟫² dν ≤ ‖v‖²` for every `v` (for centered `ν`, this is `Cov ν ≤ Id`),
and let `R ≥ 1` satisfy the Taylor bound (29) for every `u ∈ L²(ν)` in the Hilbert–Schmidt norm
of the standard basis. Then `C_P(ν) ≤ K R²` with `K = taylorCriterionConstant`.

`C_P(ν) ≤ 1/a` is finite (`literatureConstant_le_inv`); the case `C_P(ν) = 0` is trivial, and
otherwise the iterates of an approximate first eigenfunction give the bound through
`le_of_iterate_bounds`, with Lemma 3.8 from `norm_taylorField_grad0_iter_sq_le` and Lemma 3.9
from `sum_meanGradSq_iter_le`. Centering of `ν` is not needed. -/
theorem solution
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : U.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    {a : ℝ} (ha : 0 < a) (hUa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (hcov : ∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2)
    {R : ℝ} (hR : 1 ≤ R)
    (h29 : ∀ (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ), 1 ≤ d →
      ‖FunctionalInequalities.Analysis.Tensor.coordTensor (stdOrthonormalBasis ℝ V) (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (ν : Measure V) (⇑u) d)‖ ≤
        R ^ d * ‖u‖) :
    FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤
      ENNReal.ofReal (FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorCriterionConstant * R ^ 2) := by
  have hU2 : ContDiff ℝ 2 U := hU.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfin := FunctionalInequalities.KLS.LogConcave.literatureConstant_le_inv m hν hi hνU hU2 ha hUa
  have hne : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin
  set C : NNReal := (FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν).toNNReal with hCdef
  have hCP : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν = (C : ENNReal) :=
    (ENNReal.coe_toNNReal hne).symm
  rcases eq_zero_or_pos C with hC0 | hCpos
  · rw [hCP, hC0, ENNReal.coe_zero]
    exact zero_le
  · rw [hCP, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (coe_le_of_eq m hν hi hνU hU hexp ha hUa hcov hR
      h29 hCpos hCP)
