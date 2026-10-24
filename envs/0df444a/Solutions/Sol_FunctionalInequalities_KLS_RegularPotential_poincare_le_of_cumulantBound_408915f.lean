-- Prove2me | solution 1 for FunctionalInequalities.KLS.RegularPotential.poincare_le_of_cumulantBound_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:17:03.597759+00:00
-- url     : https://prove2.me/submissions/ca73e85b-4e69-4828-9468-9708ef41efaf

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Log
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_TemperateGrowth
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_LinearEquiv
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Translation
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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Derivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Law
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Growth
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Hessian
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Posterior
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Regular
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_RegularApproximation
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Hessian
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Markov
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Regular_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Regular_Isometry
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Translation
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Statement
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_AffineDecomposition
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_CovarianceGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LipschitzGradient_Comparison
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_IntrinsicTranslation
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_Laplace
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_QuadraticTilt
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
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
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Tilted
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_convexOn_of_hessian_ge_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_coordTensor_sq_eq_408915f
import Theorems.Thm_FunctionalInequalities_KLS_Isotropic_norm_coordTensor_taylorTensor_one_le_of_entries_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_taylorCriterion_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_norm_coordTensor_taylorTensor_sq_le_two_mul_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_interior_support_nonempty_of_eq_tilted_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_isBorellDensity_of_eq_tilted_408915f
import Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_integrable_exp_mul_norm_408915f
import Theorems.Thm_FunctionalInequalities_KLS_coordTensor_taylorTensor_one_apply_408915f

section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
section Moments
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- For an isotropic law the raw second moments are `∫ ⟪u, x⟫ ⟪v, x⟫ = ⟪u, v⟫`. -/
theorem FunctionalInequalities.KLS.Isotropic.integral_inner_mul_inner
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : ProbabilityMeasure E}
    (hν : Isotropic ν) (u v : E) :
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) = ⟪u, v⟫ := by
  calc
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) =
        ∫ x, ⟪u, x - ∫ y, id y ∂(ν : Measure E)⟫ *
          ⟪v, x - ∫ y, id y ∂(ν : Measure E)⟫ ∂(ν : Measure E) := by
      simp [hν.mean_zero]
    _ = ProbabilityTheory.covarianceBilin (ν : Measure E) u v := by
      rw [ProbabilityTheory.covarianceBilin_apply hν.memLp_two]
    _ = ⟪u, v⟫ := by
      rw [← Covariance.operator_inner, hν.covariance_identity]
      simp
end Moments
end
end
end
end

section
noncomputable section
open MeasureTheory Set
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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : ProbabilityMeasure V}
/-- A law `ν = volume.tilted (-W)` with continuous convex `W` is log-concave: its density
`e^{-W} / ∫ e^{-W}` is a log-concave Borell density (`IsBorellDensity.compactLogConcave`). -/
theorem FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_tilted {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) : LogConcave ν := by
  exact
    IsBorellDensity.compactLogConcave
      (isBorellDensity_of_eq_tilted_408915f hνW hW hconv)
end
end
end
end
end

section
noncomputable section
open Finset
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- **Basis independence of the Hilbert–Schmidt norm.** The Euclidean norm of the coefficient
array of a real multilinear form is the same in any two orthonormal bases. -/
theorem FunctionalInequalities.Analysis.Tensor.norm_coordTensor_eq {n n' k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (b' : OrthonormalBasis (Fin n') ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    ‖coordTensor b Φ‖ = ‖coordTensor b' Φ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [sum_coordTensor_sq_eq_408915f b b' Φ]
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
  FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section
namespace FunctionalInequalities.KLS.RegularPotential
end FunctionalInequalities.KLS.RegularPotential
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.RegularPotential
variable {V : E → ℝ} {a b : ℝ}
theorem FunctionalInequalities.KLS.RegularPotential.logConcave_law (hV : RegularPotential V a b) : LogConcave hV.law := by
  have hW : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  exact LogConcave.logConcave_of_eq_tilted (ν := hV.law) rfl hW.continuous
    (Analysis.BakryEmery.convexOn_of_hessian_ge_408915f hW hV.pos.le hV.lower)
theorem FunctionalInequalities.KLS.RegularPotential.interior_support_law (hV : RegularPotential V a b) :
    (interior ((hV.law : ProbabilityMeasure E) : Measure E).support).Nonempty := by
    change
      (interior
        (((volume : Measure E).tilted (-V)).support)).Nonempty
    exact
      FunctionalInequalities.KLS.LogConcave.interior_support_nonempty_of_eq_tilted_408915f
        (volume : Measure E) (ν := hV.law) rfl
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
end
end
end
end
end

section
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
namespace FunctionalInequalities.KLS.RegularPotential
end FunctionalInequalities.KLS.RegularPotential
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.RegularPotential
open FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.PoissonIterate
/-- **BKL Theorem 3.1** (arXiv:2610.05474v1, p. 10, proof p. 17, operator route), the exact
statement `M` of the route file, with `K = taylorCriterionConstant`: for every regular potential
`V` on `ℝⁿ` (BKL (12)) whose law `μ` is centered with `Cov μ ≤ Id`, and every `R ≥ 1` with
`|T_d f| ≤ R^d ‖f‖_{L²(μ)}` for all `f ∈ L²(μ)` and `d ≥ 1` (29) (Hilbert–Schmidt norm in the
standard basis), `C_P(μ) ≤ K R²`.

The law is `volume.tilted (-V)`; (29) passes from functions to `L²` classes (`Lp.memLp`,
`Lp.norm_def`) and from `EuclideanSpace.basisFun` to `stdOrthonormalBasis`
(`norm_coordTensor_eq`), and `taylorCriterion` applies; the centering hypothesis is not used. -/
theorem FunctionalInequalities.KLS.RegularPotential.poincare_le_of_taylor :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ)
      (hV : KLS.RegularPotential V a b),
      (∫ x, x ∂(hV.law : Measure (EuclideanSpace ℝ (Fin n)))) = 0 →
      (∀ v : EuclideanSpace ℝ (Fin n),
        ∫ x, ⟪v, x⟫ ^ 2 ∂(hV.law : Measure (EuclideanSpace ℝ (Fin n))) ≤ ‖v‖ ^ 2) →
      ∀ R : ℝ, 1 ≤ R →
      (∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
        MemLp f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin n))) → ∀ d : ℕ, 1 ≤ d →
        ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
            (taylorTensor (hV.law : Measure (EuclideanSpace ℝ (Fin n))) f d)‖ ≤
          R ^ d * (eLpNorm f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin n)))).toReal) →
      Poincare.LocalSlope.Intrinsic.constant hV.law ≤ ENNReal.ofReal (K * R ^ 2) := by
  refine ⟨taylorCriterionConstant, by norm_num [taylorCriterionConstant], fun n V a b hV _ hcov R hR h29 => ?_⟩
  have hνU : (hV.law : Measure (EuclideanSpace ℝ (Fin n))) = volume.tilted (-V) := rfl
  refine taylorCriterion_408915f volume hV.logConcave_law hV.interior_support_law
    hνU hV.temperate hV.integrable_exp_mul_norm_408915f hV.pos hV.lower hcov hR (fun u d hd => ?_)
  rw [norm_coordTensor_eq _ (EuclideanSpace.basisFun (Fin n) ℝ), Lp.norm_def]
  exact h29 u (Lp.memLp u) d hd
end
end
end
end
end

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
/-- **BKL p. 30, the case `d = 1`**: for an isotropic law on `ℝⁿ` with all exponential moments and
`f ∈ L²(μ)`, `‖T_1 f‖_HS ≤ ‖f‖_{L²(μ)}` (Bessel; assembly of the two previous lemmas). -/
theorem FunctionalInequalities.KLS.Isotropic.norm_coordTensor_taylorTensor_one_le {n : ℕ}
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hiso : Isotropic μ)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (μ : Measure (EuclideanSpace ℝ (Fin n))))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
        (taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1)‖ ≤
      (eLpNorm f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal :=
  hiso.norm_coordTensor_taylorTensor_one_le_of_entries_408915f hf fun i =>
    coordTensor_taylorTensor_one_apply_408915f (μ : Measure (EuclideanSpace ℝ (Fin n))) hexp
      hiso.memLp_two hiso.mean_zero hf i
end
end
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.RegularPotential
end FunctionalInequalities.KLS.RegularPotential
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.RegularPotential
/-- `2 K^d ≤ (2K)^d` for `d ≥ 1` and `K ≥ 0` (numeric step of BKL p. 30). -/
theorem FunctionalInequalities.KLS.RegularPotential.two_mul_pow_le_two_mul_pow {K : ℝ} (hK : 0 ≤ K) {d : ℕ} (hd : 1 ≤ d) :
    2 * K ^ d ≤ (2 * K) ^ d := by
    have hpow : (2 : ℝ) ≤ 2 ^ d :=
      le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : d ≠ 0)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hpow (pow_nonneg hK d)
namespace FunctionalInequalities.KLS.RegularPotential
end FunctionalInequalities.KLS.RegularPotential
open FunctionalInequalities.KLS.RegularPotential in
/-- **BKL p. 30: Theorem 1.1 for regular isotropic laws, conditional on the cumulant bounds of
Theorem 4.1.** If `R^ν_{d+1} ≤ (d!)² K^d · Id` for every isotropic log-concave `ν` in every dimension
and every `d ≥ 2` (`CumulantBound d ((d!)² K^d)`, `K ≥ 1`), then every isotropic regular law on `ℝⁿ`
has literature Poincaré constant at most `2 C K`, where `C` is the constant of Theorem 3.1
(`poincare_le_of_taylor`): Proposition 7.1 gives `|T_d f|² ≤ 2K^d‖f‖² ≤ (2K)^d‖f‖²` for `d ≥ 2`,
isotropy gives `|T_1 f| ≤ ‖f‖`, and Theorem 3.1 applies with `R = √(2K)`. The hypothesis is the
source's Theorem 4.1, discharged in the closed producer `BKL.Localization.exists_isotropicBound`. -/
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
      (∀ d : ℕ, 2 ≤ d → FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * K ^ d)) →
      ∀ (n : ℕ) (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ) (hV : FunctionalInequalities.KLS.RegularPotential V a b),
        FunctionalInequalities.KLS.Isotropic hV.law →
        FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant hV.law ≤ ENNReal.ofReal (2 * C * K) := by
    obtain ⟨C, hC, hT⟩ := FunctionalInequalities.KLS.RegularPotential.poincare_le_of_taylor
    refine ⟨C, hC, fun K hK hcb n V a b hV hiso => ?_⟩
    let E := EuclideanSpace ℝ (Fin n)
    have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
    let R : ℝ := Real.sqrt (2 * K)
    have hR2 : R ^ 2 = 2 * K := by
      dsimp [R]
      exact Real.sq_sqrt (by positivity)
    have hR1 : 1 ≤ R := by
      have hRnonneg : 0 ≤ R := by
        dsimp [R]
        exact Real.sqrt_nonneg _
      nlinarith [hR2]
    have hmean : (∫ x : E, x ∂(hV.law : Measure E)) = 0 := by
      exact hiso.mean_zero
    have hcov :
        ∀ v : E,
          (∫ x : E, ⟪v, x⟫ ^ 2 ∂(hV.law : Measure E)) ≤ ‖v‖ ^ 2 := by
      intro v
      have hv := hiso.integral_inner_mul_inner v v
      have hv' :
          (∫ x : E, ⟪v, x⟫ ^ 2 ∂(hV.law : Measure E)) = ‖v‖ ^ 2 := by
        simpa [pow_two, real_inner_self_eq_norm_sq] using hv
      exact hv'.le
    have htaylor :
        ∀ f, MemLp f 2 (hV.law : Measure E) →
          ∀ d : ℕ, 1 ≤ d →
            ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure E) f d)‖ ≤
              R ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal := by
      intro f hf d hd
      rcases Nat.lt_or_ge d 2 with hlt | hge
      · have hd1 : d = 1 := by omega
        subst d
        have hone :=
          hiso.norm_coordTensor_taylorTensor_one_le
            hV.integrable_exp_mul_norm_408915f hf
        have hE :
            0 ≤ (eLpNorm f 2 (hV.law : Measure E)).toReal :=
          ENNReal.toReal_nonneg
        have hR1' : 1 ≤ R ^ (1 : ℕ) := by
          simpa using hR1
        exact hone.trans (le_mul_of_one_le_left hE hR1')
      · have hparam : 0 < (d.factorial : ℝ) ^ 2 * K ^ d := by
          positivity
        have hsquare :=
          FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_two_mul_408915f hge hparam
            (hcb d hge) V hV hiso f hf
        have hfac : (d.factorial : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.factorial_ne_zero d)
        have hcancel :
            2 * ((d.factorial : ℝ) ^ 2 * K ^ d) /
                (d.factorial : ℝ) ^ 2 *
                (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 =
              2 * K ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := by
          field_simp [hfac]
        have hsq :
            ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure E) f d)‖ ^ 2 ≤
              2 * K ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := by
          calc
            ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure E) f d)‖ ^ 2
                ≤ 2 * ((d.factorial : ℝ) ^ 2 * K ^ d) /
                    (d.factorial : ℝ) ^ 2 *
                    (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := hsquare
            _ = 2 * K ^ d *
                  (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := hcancel
        have hpow : 2 * K ^ d ≤ (2 * K) ^ d :=
          FunctionalInequalities.KLS.RegularPotential.two_mul_pow_le_two_mul_pow (le_of_lt hKpos) hd
        have hsq' :
            ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure E) f d)‖ ^ 2 ≤
              (R ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal) ^ 2 := by
          calc
            ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure E) f d)‖ ^ 2
                ≤ 2 * K ^ d *
                    (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := hsq
            _ ≤ (2 * K) ^ d *
                  (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := by
              exact mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
            _ = (R ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal) ^ 2 := by
              have hp : (2 * K) ^ d = (R ^ d) ^ 2 := by
                calc
                  (2 * K) ^ d = (R ^ 2) ^ d := by rw [hR2]
                  _ = R ^ (2 * d) := by rw [pow_mul]
                  _ = R ^ (d * 2) := by
                    rw [show 2 * d = d * 2 by omega]
                  _ = (R ^ d) ^ 2 := by rw [pow_mul]
              rw [hp]
              ring
        have hnonneg :
            0 ≤ ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure E) f d)‖ :=
          norm_nonneg _
        have hright :
            0 ≤ R ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal := by
          exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
        nlinarith
    have hmain := hT n V a b hV hmean hcov R hR1 htaylor
    calc
      FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant hV.law
          ≤ ENNReal.ofReal (C * R ^ 2) := hmain
      _ = ENNReal.ofReal (2 * C * K) := by
        rw [hR2]
        congr 1
        ring
