-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.localSlope_le_of_regular_isotropic_bound_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:47:30.469443+00:00
-- url     : https://prove2.me/submissions/1cddd7e9-b19c-4b67-9c79-6bb8e01766aa

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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
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
import Theorems.Thm_FunctionalInequalities_Analysis_exists_metric_diagonal_408915f
import Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_relaxation_eq_ofLinearPMap_408915f
import Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_relaxation_le_mul_lipschitz_408915f
import Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_relaxation_mapContinuousLinearEquiv_408915f
import Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_relaxation_translateLaw_408915f
import Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_Test_exists_ambient_extension_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_row_joint_tendsto_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_covarianceBilin_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_integral_bounded_tendsto_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_mean_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_norm_sq_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_interior_support_nonempty_of_eq_tilted_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_isBorellDensity_of_eq_tilted_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_localSlope_constant_le_of_tendsto_408915f
import Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_covariance_pos_408915f
import Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_isotropic_comp_affine_of_whitening_408915f
import Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_law_comp_affine_408915f
import Theorems.Thm_FunctionalInequalities_Poincare_L2Energy_Holds_of_energy_le_mul_408915f
import Theorems.Thm_FunctionalInequalities_Poincare_L2Energy_constant_eq_of_linearIsometryEquiv_408915f
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_constant_eq_lipschitz_408915f
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_holds_iff_localSlope_408915f
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_holds_iff_preEnergy_408915f
import Theorems.Thm_FunctionalInequalities_Poincare_TestFamily_holds_ofPreEnergy_iff_408915f
import Theorems.Thm_FunctionalInequalities_Probability_affineSupport_intrinsicMeasure_408915f
import Theorems.Thm_FunctionalInequalities_exists_whitening_of_isSymmetric_408915f

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology E] [FiniteDimensional ℝ E]
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
omit [BorelSpace E] in
/-- The barycenter of a probability law with finite second moment lies in its affine support. -/
theorem FunctionalInequalities.Probability.integral_id_mem_affineSupport (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) : (∫ x, x ∂(μ : Measure E)) ∈ affineSupport μ :=
  (affineSupport μ).convex.integral_mem (isClosed_affineSupport μ) (ae_mem_affineSupport μ)
    (hμ.integrable (by norm_num))
end
end
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Covariance
end FunctionalInequalities.Covariance
open FunctionalInequalities FunctionalInequalities.Covariance
open Probability
/-- The ambient covariance operator annihilates the orthogonal complement of the direction of the
affine support. -/
theorem FunctionalInequalities.Covariance.operator_apply_eq_zero_of_mem_orthogonal (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) {w : E} (hw : w ∈ (affineSupport μ).directionᗮ) :
    operator (μ : Measure E) w = 0 := by
  apply ext_inner_right ℝ
  intro y
  rw [operator_inner, inner_zero_left, covarianceBilin_apply hμ]
  have hm : (∫ x, id x ∂(μ : Measure E)) ∈ affineSupport μ := integral_id_mem_affineSupport μ hμ
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_mem_affineSupport μ] with z hz
  have hdir : z - ∫ x, id x ∂(μ : Measure E) ∈ (affineSupport μ).direction :=
    AffineSubspace.vsub_mem_direction hz hm
  show inner ℝ w (z - ∫ x, id x ∂(μ : Measure E)) * inner ℝ y (z - ∫ x, id x ∂(μ : Measure E)) = 0
  rw [Submodule.inner_left_of_mem_orthogonal hdir hw, zero_mul]
end
end
end
end

section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- An injective covariance operator forces full affine support. -/
theorem FunctionalInequalities.Probability.affineSupport_eq_top_of_covariance_injective (μ : ProbabilityMeasure E)
    (h2 : MemLp id 2 (μ : Measure E)) (hinj : Function.Injective (Covariance.operator (μ : Measure E))) :
    Probability.affineSupport μ = ⊤ := by
  have hperp : (Probability.affineSupport μ).directionᗮ = ⊥ := by
    apply bot_unique
    intro w hw
    have h := Covariance.operator_apply_eq_zero_of_mem_orthogonal μ h2 hw
    have hz : w = 0 := hinj (h.trans (map_zero _).symm)
    simpa only [Submodule.mem_bot] using hz
  have hdir : (Probability.affineSupport μ).direction = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hperp
  have hne : (Probability.affineSupport μ : Set E).Nonempty :=
    ⟨Probability.origin μ, (Probability.origin μ).property⟩
  exact (AffineSubspace.direction_eq_top_iff_of_nonempty hne).mp hdir
end
end

section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- An isotropic law has full affine support. -/
theorem FunctionalInequalities.KLS.Isotropic.affineSupport_eq_top {μ : ProbabilityMeasure E} (hiso : KLS.Isotropic μ) :
    Probability.affineSupport μ = ⊤ := by
  apply Probability.affineSupport_eq_top_of_covariance_injective μ hiso.memLp_two
  rw [hiso.covariance_identity]
  exact fun _ _ h => h
end
end
end

section
noncomputable section
open MeasureTheory Set Topology
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
omit [CompleteSpace E] in
/-- Log-concavity is retained on the direction of the affine support, even for singular
ambient laws and a zero-dimensional carrier. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsicMeasure {μ : ProbabilityMeasure E} (hμ : LogConcave μ) :
    LogConcave (Probability.intrinsicMeasure μ) :=
  hμ.of_affineIsometry_map (Probability.intrinsicMeasure μ) (Probability.reconstruct μ)
    (Probability.measurePreserving_reconstruct μ).map_eq
omit [CompleteSpace E] in
/-- The intrinsic support has nonempty interior. This includes the singleton topology in
dimension zero and does not assert that the boundary has zero probability mass. -/
theorem FunctionalInequalities.KLS.LogConcave.interior_intrinsic_support_nonempty {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) :
    (interior (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support).Nonempty := by
  apply hμ.intrinsicMeasure.convex_support.interior_nonempty_iff_affineSpan_eq_top.mpr
  exact Probability.affineSupport_intrinsicMeasure_408915f μ
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Metric Set Topology
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
section Intrinsic
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [FiniteDimensional ℝ F]
omit [CompleteSpace F] in
/-- Every compact-set log-concave probability law is absolutely continuous in its own affine
support coordinates. Singular ambient measures and the zero-dimensional support are included. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsic_absolutelyContinuous {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) (m : Measure (Probability.affineSupport μ).direction)
    [m.IsAddHaarMeasure] :
    (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m :=
  hμ.intrinsicMeasure.absolutelyContinuous_of_interior_support_nonempty m
    hμ.interior_intrinsic_support_nonempty
end Intrinsic
end
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
/-- The centered representative is pointwise `f - mean μ f` almost everywhere. -/
theorem FunctionalInequalities.L2.center_coeFn (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ f =ᵐ[(μ : Measure α)] fun x ↦ f x - mean μ f := by
  exact (Lp.coeFn_sub f (const μ (mean μ f))).trans
    (ae_eq_rfl.sub (const_coeFn μ (mean μ f)))
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
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
universe u v
section
namespace FunctionalInequalities.L2.Translation
end FunctionalInequalities.L2.Translation
open FunctionalInequalities FunctionalInequalities.L2 FunctionalInequalities.L2.Translation
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (ν : ProbabilityMeasure V) (c : V)
omit [InnerProductSpace ℝ V] in
theorem FunctionalInequalities.L2.Translation.pullback_coeFn (f : Lp ℝ 2 (Probability.translateLaw ν c : Measure V)) :
    pullback ν c f =ᵐ[(ν : Measure V)] fun x ↦ f (c + x) :=
  Lp.coeFn_compMeasurePreserving f (Probability.measurePreserving_translate ν c)
omit [InnerProductSpace ℝ V] in
/-- Pullback along the translation preserves the intrinsic `L²` variance. -/
theorem FunctionalInequalities.L2.Translation.variance_pullbackEquiv
    (f : Lp ℝ 2 (Probability.translateLaw ν c : Measure V)) :
    L2.variance ν (pullbackEquiv ν c f) = L2.variance (Probability.translateLaw ν c) f := by
  apply NNReal.eq
  rw [L2.coe_variance_eq_pointwise, L2.coe_variance_eq_pointwise, pullbackEquiv_apply,
    ProbabilityTheory.variance_congr (pullback_coeFn ν c f)]
  exact (Probability.measurePreserving_translate ν c).variance_fun_comp
    (Lp.aestronglyMeasurable f).aemeasurable
end
section
namespace FunctionalInequalities.L2.ContinuousLinearEquiv
end FunctionalInequalities.L2.ContinuousLinearEquiv
open FunctionalInequalities FunctionalInequalities.L2 FunctionalInequalities.L2.ContinuousLinearEquiv
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
theorem FunctionalInequalities.L2.ContinuousLinearEquiv.pullback_coeFn (f : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂)) :
    pullback ν T f =ᵐ[(ν : Measure V₁)] fun x ↦ f (T x) :=
  Lp.coeFn_compMeasurePreserving f (Probability.measurePreserving_mapContinuousLinearEquiv ν T)
/-- Pullback along `T` preserves the intrinsic `L²` variance. -/
theorem FunctionalInequalities.L2.ContinuousLinearEquiv.variance_pullbackEquiv
    (f : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂)) :
    L2.variance ν (pullbackEquiv ν T f) = L2.variance (Probability.mapContinuousLinearEquiv ν T) f := by
  apply NNReal.eq
  rw [L2.coe_variance_eq_pointwise, L2.coe_variance_eq_pointwise, pullbackEquiv_apply,
    ProbabilityTheory.variance_congr (pullback_coeFn ν T f)]
  exact (Probability.measurePreserving_mapContinuousLinearEquiv ν T).variance_fun_comp
    (Lp.aestronglyMeasurable f).aemeasurable
end
end
end
end
end

section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.Functional
end FunctionalInequalities.Energy.Functional
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.Functional
variable {X : Type*}
/-- Membership in the domain is the finiteness predicate. -/
@[simp]
theorem FunctionalInequalities.Energy.Functional.mem_domain (energy : Functional X) (x : X) :
    x ∈ energy.domain ↔ energy.FiniteAt x :=
  Iff.rfl
end
end
end
end

section
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
universe u
section
namespace FunctionalInequalities.Poincare.TestFamily
end FunctionalInequalities.Poincare.TestFamily
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.TestFamily
/-- The extended Rayleigh quotient is bounded by a finite `C` exactly when the defining
inequality holds. This includes zero-energy tests, whose quotient may be infinite. -/
theorem FunctionalInequalities.Poincare.TestFamily.rayleigh_le_iff (F : TestFamily) (f : F.Test) (C : NNReal) :
    rayleigh F f ≤ (C : ENNReal) ↔ F.variance f ≤ C * F.energy f := by
  rw [rayleigh, ENNReal.div_le_iff_le_mul
    (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top), ← ENNReal.coe_mul,
    ENNReal.coe_le_coe]
/-- A finite constant is valid exactly when it bounds the optimal extended constant. -/
theorem FunctionalInequalities.Poincare.TestFamily.holds_iff_constant_le (F : TestFamily) (C : NNReal) :
    Holds F C ↔ constant F ≤ (C : ENNReal) := by
  rw [constant, iSup_le_iff]
  exact forall_congr' fun f ↦ (rayleigh_le_iff F f C).symm
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
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
universe u
variable {α : Type u} [MeasurableSpace α]
section
namespace FunctionalInequalities.Poincare.L2Energy
end FunctionalInequalities.Poincare.L2Energy
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.L2Energy
/-- A finite `L²` Poincaré constant is valid exactly when it bounds the optimal one. -/
theorem FunctionalInequalities.Poincare.L2Energy.holds_iff_constant_le (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) (C : NNReal) :
    Holds μ energy C ↔ constant μ energy ≤ (C : ENNReal) := by
  simpa [Holds, constant] using
    TestFamily.holds_iff_constant_le (TestFamily.ofL2Energy μ energy) C
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
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.CovarianceGradient
end FunctionalInequalities.Poincare.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.CovarianceGradient
open Energy.CovarianceGradient
universe u v
section Translation
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V]
  (ν : ProbabilityMeasure V) (c : V)
/-- The optimal `L²` Poincaré constant of the covariance relaxation is translation invariant. -/
theorem FunctionalInequalities.Poincare.CovarianceGradient.constant_translateLaw :
    Poincare.L2Energy.constant (Probability.translateLaw ν c) (relaxation (Probability.translateLaw ν c)) =
      Poincare.L2Energy.constant ν (relaxation ν) :=
  Poincare.L2Energy.constant_eq_of_linearIsometryEquiv_408915f ν (Probability.translateLaw ν c)
    (relaxation ν) (relaxation (Probability.translateLaw ν c)) (L2.Translation.pullbackEquiv ν c)
    (L2.Translation.variance_pullbackEquiv ν c) (relaxation_translateLaw_408915f ν c)
end Translation
section LinearEquiv
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
  [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁]
  {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
  [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂]
  (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
omit [SecondCountableTopology V₁] in
/-- The optimal `L²` Poincaré constant of the covariance relaxation is invariant under continuous
linear equivalences. -/
theorem FunctionalInequalities.Poincare.CovarianceGradient.constant_mapContinuousLinearEquiv :
    Poincare.L2Energy.constant (Probability.mapContinuousLinearEquiv ν T) (relaxation (Probability.mapContinuousLinearEquiv ν T)) =
      Poincare.L2Energy.constant ν (relaxation ν) :=
  Poincare.L2Energy.constant_eq_of_linearIsometryEquiv_408915f ν (Probability.mapContinuousLinearEquiv ν T)
    (relaxation ν) (relaxation (Probability.mapContinuousLinearEquiv ν T)) (L2.ContinuousLinearEquiv.pullbackEquiv ν T)
    (L2.ContinuousLinearEquiv.variance_pullbackEquiv ν T) (relaxation_mapContinuousLinearEquiv_408915f ν T)
end LinearEquiv
end
end
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.LocalSlope
end FunctionalInequalities.Poincare.LocalSlope
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.LocalSlope
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
omit [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E]
  [SecondCountableTopology E] [FiniteDimensional ℝ E] in
/-- All tests on a zero-dimensional coordinate space have zero variance. -/
theorem FunctionalInequalities.Poincare.LocalSlope.holds_zero_of_subsingleton [Subsingleton E] (ν : ProbabilityMeasure E) :
    Holds ν 0 := by
  intro f _
  have hf : f = fun _ ↦ f 0 := funext fun y ↦ congrArg f (Subsingleton.elim y 0)
  rw [hf]
  simp [evariance]
omit [CompleteSpace E] in
/-- The literature optimum includes the zero-dimensional case with value zero. -/
theorem FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_subsingleton [Subsingleton E] (μ : ProbabilityMeasure E) :
    Poincare.LocalSlope.Intrinsic.constant μ = 0 := by
  apply le_antisymm ?_ bot_le
  exact iInf_le_of_le ⟨0, Poincare.LocalSlope.holds_zero_of_subsingleton (Probability.intrinsicMeasure μ)⟩
    (by simp)
end
end
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [MeasurableSpace E]
/-- Source: local order consequence of `constant` and Mathlib's `iInf_le_of_le`.
Every finite valid constant bounds the optimal constant from above. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_le {μ : Measure E} {C : NNReal}
    (hC : Holds μ (C : ℝ)) :
    constant μ ≤ (C : ENNReal) := by
  exact iInf_le_of_le ⟨C, hC⟩ le_rfl
/-- Source: local order consequence of `constant` and Mathlib's `le_iInf`.
A lower bound for every finite valid constant bounds the optimal constant from below. -/
theorem FunctionalInequalities.Poincare.SmoothTest.le_constant {μ : Measure E} {L : ENNReal}
    (hL : ∀ C : NNReal, Holds μ (C : ℝ) → L ≤ (C : ENNReal)) :
    L ≤ constant μ := by
  refine le_iInf fun C ↦ ?_
  exact hL C.1 C.2
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.SmoothGradient
end FunctionalInequalities.Energy.SmoothGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.SmoothGradient
open Euclidean
universe u
private theorem FunctionalInequalities.Energy.SmoothGradient.pullbackTest_energy_le
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] [MeasurableSpace Y]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} (f : Test ν)
    (φ : X → Y) (hφ : ContDiff ℝ ∞ φ) (hlip : LipschitzWith 1 φ)
    (hmp : MeasurePreserving φ (μ : Measure X) (ν : Measure Y)) :
    (FunctionalInequalities.Energy.SmoothGradient.pullbackTest f φ hφ hlip hmp).energy ≤ f.energy := by
  apply NNReal.coe_le_coe.mp
  calc
    _ ≤ ∫ x, ‖gradient f (φ x)‖ ^ 2 ∂(μ : Measure X) := by
      apply integral_mono (FunctionalInequalities.Energy.SmoothGradient.pullbackTest f φ hφ hlip hmp).gradient_sq_integrable
        (hmp.integrable_comp_of_integrable f.gradient_sq_integrable)
      intro x
      exact pow_le_pow_left₀ (norm_nonneg _) (FunctionalInequalities.Energy.SmoothGradient.norm_gradient_comp_le f.contDiff hφ hlip x) 2
    _ = _ := by
      have h := integral_map hmp.measurable.aemeasurable
        (hmp.map_eq.symm ▸ f.gradient_sq_integrable.aestronglyMeasurable)
      simpa only [hmp.map_eq, Test.coe_energy] using h.symm
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : ProbabilityMeasure E)
section
namespace FunctionalInequalities.Energy.SmoothGradient.Test
end FunctionalInequalities.Energy.SmoothGradient.Test
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.SmoothGradient FunctionalInequalities.Energy.SmoothGradient.Test
/-- Restriction has the expected `L²` realization and does not increase raw energy.
Source: the tangential-gradient projection argument in the local Blueprint comparison. -/
theorem FunctionalInequalities.Energy.SmoothGradient.Test.exists_intrinsic_restriction (f : Energy.SmoothGradient.Test μ) :
    ∃ g : Energy.SmoothGradient.Test (Probability.intrinsicMeasure μ),
      (∀ v, g v = f (Probability.reconstruct μ v)) ∧
      g.toL2 = toIntrinsicL2 μ f.toL2 ∧ g.energy ≤ f.energy := by
  let φ := Probability.reconstruct μ
  have hφ : ContDiff ℝ ∞ φ := φ.toContinuousAffineMap.contDiff
  let g := FunctionalInequalities.Energy.SmoothGradient.pullbackTest f φ hφ φ.isometry.lipschitz
    (Probability.measurePreserving_reconstruct μ)
  exact ⟨g, fun _ ↦ rfl, rfl,
    pullbackTest_energy_le f φ hφ φ.isometry.lipschitz
      (Probability.measurePreserving_reconstruct μ)⟩
end
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
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothGradient
end FunctionalInequalities.Poincare.SmoothGradient
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothGradient
section
namespace FunctionalInequalities.Poincare.SmoothGradient.Ambient
end FunctionalInequalities.Poincare.SmoothGradient.Ambient
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothGradient FunctionalInequalities.Poincare.SmoothGradient.Ambient
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]
/-- A finite constant is valid for the smooth-gradient relaxation exactly when it bounds its
optimal extended constant. -/
theorem FunctionalInequalities.Poincare.SmoothGradient.Ambient.holds_iff_constant_le (μ : ProbabilityMeasure E)
    [FiniteDimensional ℝ E] [BorelSpace E] [SecondCountableTopology E] (C : NNReal) :
    Holds μ C ↔
      constant μ ≤ (C : ENNReal) := by
  exact L2Energy.holds_iff_constant_le μ (Energy.SmoothGradient.relaxation μ) C
end
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
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : ProbabilityMeasure E)
/-- Smooth-test and ambient relaxed inequalities have the same valid finite constants.
Source: Blueprint `thm:legacy-relaxed-holds-equivalence` and the abstract pre-energy bridge. -/
theorem FunctionalInequalities.Poincare.SmoothTest.holds_iff_ambient (C : NNReal) :
    Holds (μ : Measure E) (C : ℝ) ↔ Poincare.SmoothGradient.Ambient.Holds μ C := by
  exact (holds_iff_preEnergy_408915f μ C).trans
    (TestFamily.holds_ofPreEnergy_iff_408915f μ (Energy.SmoothGradient.preEnergy μ) C)
/-- The smooth-test infimum equals the ambient relaxed Rayleigh supremum, also at infinity.
Source: equality of the sets of valid finite constants; no attainment assumption is needed. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_eq_ambient :
    constant (μ : Measure E) = Poincare.SmoothGradient.Ambient.constant μ := by
  apply le_antisymm
  · by_cases h : Poincare.SmoothGradient.Ambient.constant μ = ⊤
    · simp [h]
    · have hcoe := ENNReal.coe_toNNReal h
      have hbound := (Poincare.SmoothGradient.Ambient.holds_iff_constant_le μ _).mpr hcoe.ge
      exact (constant_le ((holds_iff_ambient μ _).mpr hbound)).trans hcoe.le
  · apply le_constant
    intro C hC
    exact (Poincare.SmoothGradient.Ambient.holds_iff_constant_le μ C).mp
      ((holds_iff_ambient μ C).mp hC)
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
/-- Step 6: equality of the infima of valid finite constants on this same coordinate space.
The subtype infimum is the existing Poincare.LocalSlope.Holds definition, without a second intrinsic map. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_eq_localSlope_infimum (ν : ProbabilityMeasure E) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (hν : (ν : Measure E) ≪ m) :
    constant (ν : Measure E) =
      ⨅ C : {C : NNReal // Poincare.LocalSlope.Holds ν C}, (C.1 : ENNReal) := by
  apply le_antisymm
  · refine le_iInf fun C => ?_
    exact constant_le ((holds_iff_localSlope_408915f ν m hν C.1).mpr C.2)
  · apply le_constant
    intro C hC
    exact iInf_le_of_le ⟨C, (holds_iff_localSlope_408915f ν m hν C).mp hC⟩ le_rfl
/-- Smooth inequalities transport between the ambient law and its intrinsic law without
absolute continuity. Restriction decreases energy, while normal-constant extension preserves it. -/
private theorem FunctionalInequalities.Poincare.SmoothTest.holds_iff_intrinsicMeasure (μ : ProbabilityMeasure E) (C : NNReal) :
    Holds (μ : Measure E) (C : ℝ) ↔
      Holds (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) (C : ℝ) := by
  let ν := Probability.intrinsicMeasure μ
  have hvar (f : Energy.SmoothGradient.Test μ)
      (g : Energy.SmoothGradient.Test ν)
      (heq : ∀ v, g v = f (Probability.reconstruct μ v)) :
      ProbabilityTheory.variance g.toFun (ν : Measure (Probability.affineSupport μ).direction) =
        ProbabilityTheory.variance f.toFun (μ : Measure E) := by
    calc
      _ = ProbabilityTheory.variance (fun v => f (Probability.reconstruct μ v))
          (ν : Measure (Probability.affineSupport μ).direction) :=
        congrArg (fun k => ProbabilityTheory.variance k (ν : Measure _)) (funext heq)
      _ = _ := (Probability.measurePreserving_reconstruct μ).variance_fun_comp
        f.contDiff.continuous.aemeasurable
  constructor
  · intro h
    refine ⟨inferInstance, C.2, ?_⟩
    intro g hg
    let gt : Energy.SmoothGradient.Test ν :=
      ⟨g, hg.smooth', hg.memLp_two, hg.energy_integrable⟩
    obtain ⟨f, heq, _, henergy⟩ :=
      Energy.SmoothGradient.Test.exists_ambient_extension_408915f μ gt
    have he : energy (μ : Measure E) f.toFun = energy (ν : Measure _) gt.toFun :=
      congrArg (fun c : NNReal => (c : ℝ)) henergy
    change ProbabilityTheory.variance gt.toFun (ν : Measure _) ≤ C * energy (ν : Measure _) gt.toFun
    rw [hvar f gt (fun v => (heq v).symm), ← he]
    exact h.variance_le ⟨f.contDiff, f.memLp_two, f.gradient_sq_integrable⟩
  · intro h
    refine ⟨inferInstance, C.2, ?_⟩
    intro f hf
    let ft : Energy.SmoothGradient.Test μ :=
      ⟨f, hf.smooth', hf.memLp_two, hf.energy_integrable⟩
    obtain ⟨g, heq, _, henergy⟩ :=
      Energy.SmoothGradient.Test.exists_intrinsic_restriction μ ft
    have he : energy (ν : Measure _) g.toFun ≤ energy (μ : Measure E) ft.toFun :=
      NNReal.coe_le_coe.mpr henergy
    have hb := h.variance_le ⟨g.contDiff, g.memLp_two, g.gradient_sq_integrable⟩
    change ProbabilityTheory.variance ft.toFun (μ : Measure E) ≤ C * energy (μ : Measure E) ft.toFun
    rw [← hvar ft g heq]
    exact hb.trans (mul_le_mul_of_nonneg_left he C.2)
/-- Step 7: the exact ambient / intrinsic / literature chain from the Blueprint theorem.
Use the proved smooth-test restriction and normal-constant extension for the first equality.
The Haar reference lives on the direction of the affine support; zero dimension is included. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope (μ : ProbabilityMeasure E)
    (m : Measure (Probability.affineSupport μ).direction) [Measure.IsAddHaarMeasure m]
    (hμ : (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m) :
    constant (μ : Measure E) =
        constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ∧
      constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) =
        Poincare.LocalSlope.Intrinsic.constant μ := by
  constructor
  · apply le_antisymm
    · apply le_constant
      intro C hC
      exact constant_le ((holds_iff_intrinsicMeasure μ C).mpr hC)
    · apply le_constant
      intro C hC
      exact constant_le ((holds_iff_intrinsicMeasure μ C).mp hC)
  · exact constant_eq_localSlope_infimum (Probability.intrinsicMeasure μ) m hμ
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
open Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure]
section Bridge
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient
/-- With identity covariance, the covariance relaxation of `def:affine-poincare-constant` is the
Lipschitz gradient relaxation. -/
theorem FunctionalInequalities.Energy.CovarianceGradient.relaxation_eq_lipschitz (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (hcov : Covariance.operator (ν : Measure V) = ContinuousLinearMap.id ℝ V) :
    relaxation ν = Energy.LipschitzGradient.relaxation ν m hac :=
  relaxation_eq_ofLinearPMap_408915f ν (ContinuousLinearMap.id ℝ V) hac hfr
    (fun v ↦ by rw [hcov, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq])
end
end
end Bridge
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
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.L2Energy
end FunctionalInequalities.Poincare.L2Energy
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.L2Energy
universe u
variable {α : Type u} [MeasurableSpace α]
/-- The same finite energy comparison bounds the target's extended optimal constant. -/
theorem FunctionalInequalities.Poincare.L2Energy.constant_le_mul_of_energy_le_mul {μ : ProbabilityMeasure α}
    {source target : Energy.Functional (Lp ℝ 2 (μ : Measure α))} {C κ : NNReal}
    (hC : Holds μ source C)
    (henergy : ∀ f : target.domain,
      source f.1 ≤ (κ : ENNReal) * target f.1) :
    constant μ target ≤ ((κ * C : NNReal) : ENNReal) :=
  (holds_iff_constant_le μ target (κ * C)).mp (hC.of_energy_le_mul_408915f henergy)
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
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
/-- The ambient smooth-test, intrinsic smooth-test, and intrinsic literature optima agree
for every log-concave probability law. Absolute continuity is derived, not assumed. -/
theorem FunctionalInequalities.KLS.LogConcave.smoothTest_constant_eq_intrinsic_and_localSlope
    {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ) :
    Poincare.SmoothTest.constant (μ : Measure E) =
        Poincare.SmoothTest.constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ∧
      Poincare.SmoothTest.constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) =
        Poincare.LocalSlope.Intrinsic.constant μ :=
  Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope μ Measure.addHaar
    (hμ.intrinsic_absolutelyContinuous Measure.addHaar)
/-- The smooth-test optimum equals the literature optimum for every log-concave law. -/
theorem FunctionalInequalities.KLS.LogConcave.smoothTest_constant_eq_localSlope
    {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ) :
    Poincare.SmoothTest.constant (μ : Measure E) = Poincare.LocalSlope.Intrinsic.constant μ :=
  (smoothTest_constant_eq_intrinsic_and_localSlope hμ).1.trans
    (smoothTest_constant_eq_intrinsic_and_localSlope hμ).2
end
end
end
end
end

section
noncomputable section
open InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
section
namespace FunctionalInequalities.Covariance
end FunctionalInequalities.Covariance
open FunctionalInequalities FunctionalInequalities.Covariance
variable [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
/-- A positive definite covariance operator has a self-adjoint whitening `W` with
`⟪Σ (W u), W v⟫ = ⟪u, v⟫`, so that `W ∘ Σ ∘ W = 1`. -/
theorem FunctionalInequalities.Covariance.exists_whitening (μ : MeasureTheory.Measure V)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ (operator μ v) v) :
    ∃ W : V ≃L[ℝ] V, (W : V →L[ℝ] V).adjoint = W ∧
      ∀ u v, inner ℝ (operator μ (W u)) (W v) = inner ℝ u v := by
  refine exists_whitening_of_isSymmetric_408915f (operator μ) ?_ hpos
  intro x y
  calc inner ℝ (operator μ x) y = ProbabilityTheory.covarianceBilin μ x y := operator_inner μ x y
    _ = ProbabilityTheory.covarianceBilin μ y x := ProbabilityTheory.covarianceBilin_comm x y
    _ = inner ℝ (operator μ y) x := (operator_inner μ y x).symm
    _ = inner ℝ x (operator μ y) := real_inner_comm _ _
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
open Energy Energy.Euclidean Probability
section Euclidean
variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
  [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
  [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂]
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
omit [CompleteSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] in
/-- A log-concave law with full affine support has support with nonempty interior. -/
theorem FunctionalInequalities.KLS.LogConcave.interior_support_nonempty_of_affineSupport_eq_top {ν : ProbabilityMeasure V₁}
    (hν : LogConcave ν) (h : affineSupport ν = ⊤) :
    (interior (ν : Measure V₁).support).Nonempty :=
  hν.convex_support.interior_nonempty_iff_affineSpan_eq_top.mpr h
end
end
end Euclidean
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
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem FunctionalInequalities.KLS.RegularPotential.affineUpperConstant_pos (b : ℝ) (L : E ≃L[ℝ] E) : 0 < affineUpperConstant b L := by
  unfold affineUpperConstant
  exact mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right b 1)) (sq_pos_of_pos (by positivity))
end
end
end
end
end

section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section RegularAffineLaws
variable {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b)
include hV in
/-- The law of `V ∘ (L · + c)` as a translation followed by the continuous linear equivalence `L⁻¹`. -/
theorem FunctionalInequalities.KLS.RegularPotential.law_comp_affine_eq_map
    (L : E ≃L[ℝ] E) (c : E) :
    (RegularPotential.comp_affine hV L c).law =
      Probability.mapContinuousLinearEquiv (Probability.translateLaw hV.law (-c)) L.symm := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [RegularPotential.law_comp_affine_408915f hV L c, Probability.coe_mapContinuousLinearEquiv, Probability.coe_translateLaw,
    Measure.map_map L.symm.continuous.measurable (by fun_prop)]
  congr 1
  funext y
  change L.symm (y - c) = L.symm (-c + y)
  congr 1
  abel
end RegularAffineLaws
end
end
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
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
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.lintegral_normalizedDensity_eq_one {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ x : V, ENNReal.ofReal (normalizedDensity ρ s x) = 1 := by
  have hprob := smoothedLaw_probability (ν := ν) hs
  rw [isProbabilityMeasure_iff] at hprob
  rw [smoothedLaw_eq_withDensity_normalizedDensity hρ hs,
    withDensity_apply _ MeasurableSet.univ] at hprob
  simpa only [Measure.restrict_univ] using hprob
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integrable_normalizedDensity {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    Integrable (normalizedDensity ρ s) (volume : Measure V) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (normalizedDensity_measurable hρ.measurable hs).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (normalizedDensity_pos hρ hs x).le)).mp
  rw [lintegral_normalizedDensity_eq_one hρ hs]
  simp
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integral_normalizedDensity_eq_one {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    ∫ x : V, normalizedDensity ρ s x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (normalizedDensity_pos hρ hs x).le)
    (normalizedDensity_measurable hρ.measurable hs).aestronglyMeasurable]
  rw [lintegral_normalizedDensity_eq_one hρ hs]
  simp
/-- The normalized Gaussian convolution is exactly the tilted law of its
continuous convex logarithmic potential. Higher smoothness of the potential is a
separate analytic obligation. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_eq_tilted_potential {ν : Measure V}
    [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : IsBorellDensity ν volume ρ) {s : ℝ} (hs : 0 < s) :
    smoothedLaw ν s = (volume : Measure V).tilted (-(potential ρ s)) := by
  have hExp (x : V) : Real.exp (-potential ρ s x) =
      normalizedDensity ρ s x := by
    simp [potential, Real.exp_log (normalizedDensity_pos hρ hs x)]
  rw [smoothedLaw_eq_withDensity_normalizedDensity hρ hs]
  unfold Measure.tilted
  simp only [Pi.neg_apply]
  simp_rw [hExp]
  rw [integral_normalizedDensity_eq_one hρ hs]
  simp
end
end
end
end
end
end

section
section
open MeasureTheory ProbabilityTheory Filter Topology
open FunctionalInequalities.Analysis.BakryEmery
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
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- **Covariance of the smoothed law**: `Cov(μ * γ_s) = Cov μ + (1/(2s)) · Id` (BKL Section 2, p. 5). -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_covariance_operator (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) :
    Covariance.operator (smoothedLaw μ s) = Covariance.operator μ +
      (1 / (2 * s)) • (1 : E →L[ℝ] E) := by
  ext v
  apply ext_inner_right ℝ
  intro w
  rw [Covariance.operator_inner]
  simp only [add_apply, smul_apply, inner_add_left, real_inner_smul_left,
    Covariance.operator_inner]
  have hone : (1 : E →L[ℝ] E) v = v := rfl
  rw [hone]
  simpa only [one_div, one_mul, div_eq_mul_inv, mul_comm] using smoothedLaw_covarianceBilin_408915f μ hμ2 hs v w
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.epsilon_tendsto_zero :
    Tendsto (fun s : ℝ => 1 / (2 * s)) atTop (𝓝 (0 : ℝ)) := by
  have ht : Tendsto (fun s : ℝ => 2 * s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
  simpa only [Function.comp_def, one_div] using (tendsto_inv_atTop_zero.comp ht)
/-- The means of the smoothed laws converge (they are constant) as `s → ∞`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_mean_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) :
    Tendsto (fun s : ℝ => ∫ y : E, y ∂(smoothedLaw μ s)) atTop (𝓝 (∫ y : E, y ∂μ)) := by
  apply (tendsto_const_nhds (x := ∫ y : E, y ∂μ)).congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  exact (smoothedLaw_mean_408915f μ hμ2 hs).symm
/-- The raw second moments of the smoothed laws converge as `s → ∞`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_norm_sq_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) :
    Tendsto (fun s : ℝ => ∫ y : E, ‖y‖ ^ 2 ∂(smoothedLaw μ s)) atTop (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂μ)) := by
  have ht : Tendsto (fun s : ℝ => (∫ y : E, ‖y‖ ^ 2 ∂μ) + (Module.finrank ℝ E : ℝ) / (2 * s))
      atTop (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂μ)) := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_zero, add_zero] using
      (tendsto_const_nhds (x := ∫ y : E, ‖y‖ ^ 2 ∂μ)).add
        (epsilon_tendsto_zero.const_mul (Module.finrank ℝ E : ℝ))
  apply ht.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  exact (smoothedLaw_norm_sq_408915f μ hμ2 hs).symm
/-- The covariance operators of the smoothed laws converge in operator norm as `s → ∞`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_covariance_operator_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) :
    Tendsto (fun s : ℝ => Covariance.operator (smoothedLaw μ s)) atTop (𝓝 (Covariance.operator μ)) := by
  have ht : Tendsto (fun s : ℝ => Covariance.operator μ + (1 / (2 * s)) • (1 : E →L[ℝ] E))
      atTop (𝓝 (Covariance.operator μ)) := by
    simpa only [zero_smul, add_zero] using (tendsto_const_nhds (x := Covariance.operator μ)).add
      (epsilon_tendsto_zero.smul (tendsto_const_nhds (x := (1 : E →L[ℝ] E))))
  apply ht.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  exact (smoothedLaw_covariance_operator μ hμ2 hs).symm
end
end
end
end
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Bornology
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
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
section WeakConvergence
open Filter Topology Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- **Weak convergence of the Gaussian smoothing**: `μ * γ_{n+1} → μ` in the topology of weak
convergence of probability laws (BKL Section 2, p. 5). -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedProbabilityLaw_tendsto {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) :
    Tendsto (fun n : ℕ => smoothedProbabilityLaw μ ((n : ℝ) + 1) (by positivity)) atTop (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2
  intro f
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact (smoothedLaw_integral_bounded_tendsto_408915f hρ f).comp hn
end WeakConvergence
end
end
end
end
end
end

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
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
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] in
/-- The quadratic tilt of the smoothed law is the law of the potential `V_s + δ/2‖·‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.quadraticTilt_smoothedLaw_eq_tilted {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) (δ : ℝ) :
    (smoothedLaw μ s).tilted (fun y => -(δ / 2) * ‖y‖ ^ 2) =
      (volume : Measure E).tilted (-(fun y => potential ρ s y + δ / 2 * ‖y‖ ^ 2)) := by
  rw [smoothedLaw_eq_tilted_potential hρ hs]
  have hi : Integrable (fun y => Real.exp ((-potential ρ s) y)) (volume : Measure E) := by
    convert integrable_normalizedDensity hρ hs using 1
    funext y
    simp [potential, Real.exp_log (normalizedDensity_pos hρ hs y)]
  rw [MeasureTheory.tilted_tilted hi]
  congr 1
  funext y
  simp
  ring
/-- `2s + δ > 0`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.two_mul_add_pos {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) : 0 < 2 * s + δ := by
  linarith
/-- The law of the produced regular potential is the two-step law: Gaussian smoothing, then quadratic
tilt. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.regularLaw_eq_quadraticTilt {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : IsBorellDensity (μ : Measure E) volume ρ) {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    (regularPotential_quadraticPotential hρ hs hδ).law =
      Probability.quadraticTiltLaw (smoothedProbabilityLaw μ s hs) δ hδ.le := by
  apply Subtype.ext
  change (volume : Measure E).tilted (-quadraticPotential ρ s δ) =
    (smoothedLaw (μ : Measure E) s).tilted (fun y => -(δ / 2) * ‖y‖ ^ 2)
  exact (quadraticTilt_smoothedLaw_eq_tilted hρ hs δ).symm
end
end
end
end
end

section
open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis
noncomputable section
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
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.tiltRate_tendsto_zero : Tendsto tiltRate atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.selected_tiltRate_tendsto_zero {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) :
    Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) := tiltRate_tendsto_zero.comp hk
/-- Joint convergence of the smoothings and their statistics to those of `μ`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_joint_tendsto {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (hμ2 : MemLp id 2 (μ : Measure E)) :
    Tendsto (fun n : ℕ => (gaussianSeq μ n, statistics (gaussianSeq μ n)))
      atTop (𝓝 (μ, statistics μ)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hw := smoothedProbabilityLaw_tendsto hρ
  have hm := (smoothedLaw_mean_tendsto (μ : Measure E) hμ2).comp hn
  have hsecond := (smoothedLaw_norm_sq_tendsto (μ : Measure E) hμ2).comp hn
  have hcov := (smoothedLaw_covariance_operator_tendsto (μ : Measure E) hμ2).comp hn
  exact hw.prodMk_nhds (hm.prodMk_nhds (hsecond.prodMk_nhds hcov))
/-- A diagonal `k n ≥ n` along which the two-step laws and their statistics converge to `μ`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_diagonal_tendsto {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (hμ2 : MemLp id 2 (μ : Measure E)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ Tendsto k atTop atTop ∧
      (∀ n, 0 < tiltRate (k n)) ∧ Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n => (rowLaw μ n (k n), statistics (rowLaw μ n (k n))))
        atTop (𝓝 (μ, statistics μ)) := by
  let X := ProbabilityMeasure E × (E × (ℝ × (E →L[ℝ] E)))
  let : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  obtain ⟨k, hkl, hk, hdiag⟩ := Analysis.exists_metric_diagonal_408915f
    (fun n j => (rowLaw μ n j, statistics (rowLaw μ n j)))
    (fun n => (gaussianSeq μ n, statistics (gaussianSeq μ n)))
    (μ, statistics μ) (row_joint_tendsto_408915f μ hμ2) (gaussian_joint_tendsto hρ hμ2)
  exact ⟨k, hkl, hk, fun n => tiltRate_pos (k n), selected_tiltRate_tendsto_zero hk, hdiag⟩
/-- The diagonal with the four limits (law, mean, raw second moment, covariance) exposed. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_diagonal_limits {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (hμ2 : MemLp id 2 (μ : Measure E)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ (∀ n, 0 < tiltRate (k n)) ∧
      Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n => rowLaw μ n (k n)) atTop (𝓝 μ) ∧
      Tendsto (fun n => ∫ y : E, y ∂(rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, y ∂(μ : Measure E))) ∧
      Tendsto (fun n => ∫ y : E, ‖y‖ ^ 2 ∂(rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂(μ : Measure E))) ∧
      Tendsto (fun n => Covariance.operator (rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (Covariance.operator (μ : Measure E))) := by
  obtain ⟨k, hkl, _hk, hpos, hδ, hdiag⟩ := exists_diagonal_tendsto hρ hμ2
  exact ⟨k, hkl, hpos, hδ, hdiag.fst_nhds, hdiag.snd_nhds.fst_nhds,
    hdiag.snd_nhds.snd_nhds.fst_nhds, hdiag.snd_nhds.snd_nhds.snd_nhds⟩
/-- **Regular approximation** (BKL Section 2, p. 5): a law with a Borell density and finite second
moment is the weak limit of laws of regular potentials `V_{n+1} + δ/2‖·‖²` with curvature bounds
`δ ≤ ∇² ≤ 2(n+1) + δ`, with means, raw second moments and covariance operators converging too.
No whitened-sequence convergence is asserted. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_regular_approximation_limits
    {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (hμ2 : MemLp id 2 (μ : Measure E)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ (∀ n, 0 < tiltRate (k n)) ∧
      Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) ∧
      (∀ n : ℕ, KLS.RegularPotential
        (quadraticPotential ρ ((n : ℝ) + 1) (tiltRate (k n))) (tiltRate (k n))
        (2 * ((n : ℝ) + 1) + tiltRate (k n))) ∧
      (∀ n : ℕ, 0 < 2 * ((n : ℝ) + 1) + tiltRate (k n)) ∧
      Tendsto (fun n => rowLaw μ n (k n)) atTop (𝓝 μ) ∧
      Tendsto (fun n => ∫ y : E, y ∂(rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, y ∂(μ : Measure E))) ∧
      Tendsto (fun n => ∫ y : E, ‖y‖ ^ 2 ∂(rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂(μ : Measure E))) ∧
      Tendsto (fun n => Covariance.operator (rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (Covariance.operator (μ : Measure E))) := by
  obtain ⟨k, hkl, hpos, hδ, hw, hm, hsecond, hcov⟩ := exists_diagonal_limits hρ hμ2
  exact ⟨k, hkl, hpos, hδ, fun n => regularPotential_quadraticPotential hρ (by positivity) (hpos n),
    fun n => two_mul_add_pos (by positivity) (hpos n), hw, hm, hsecond, hcov⟩
/-- It equals the two-step law. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.regularSeq_eq_rowLaw {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (n k : ℕ) :
    regularSeq hρ n k = rowLaw μ n k :=
  regularLaw_eq_quadraticTilt hρ (by positivity) (tiltRate_pos k)
/-- The regular approximation stated for `regularSeq`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_regularSeq_limits
    {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (hμ2 : MemLp id 2 (μ : Measure E)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ (∀ n, 0 < tiltRate (k n)) ∧
      Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) ∧
      (∀ n : ℕ, KLS.RegularPotential
        (quadraticPotential ρ ((n : ℝ) + 1) (tiltRate (k n))) (tiltRate (k n))
        (2 * ((n : ℝ) + 1) + tiltRate (k n))) ∧
      (∀ n : ℕ, 0 < 2 * ((n : ℝ) + 1) + tiltRate (k n)) ∧
      Tendsto (fun n => regularSeq hρ n (k n)) atTop (𝓝 μ) ∧
      Tendsto (fun n => ∫ y : E, y ∂(regularSeq hρ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, y ∂(μ : Measure E))) ∧
      Tendsto (fun n => ∫ y : E, ‖y‖ ^ 2 ∂(regularSeq hρ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂(μ : Measure E))) ∧
      Tendsto (fun n => Covariance.operator (regularSeq hρ n (k n) : Measure E)) atTop
        (𝓝 (Covariance.operator (μ : Measure E))) := by
  simpa only [regularSeq_eq_rowLaw] using
    exists_regular_approximation_limits hρ hμ2
end
end
end
end
end
end

section
open MeasureTheory ProbabilityTheory
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
namespace FunctionalInequalities.KLS.RegularPotential
end FunctionalInequalities.KLS.RegularPotential
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.RegularPotential
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {V : E → ℝ} {a b : ℝ}
/-- Lebesgue measure is absolutely continuous with respect to a regular law (positive density). -/
theorem FunctionalInequalities.KLS.RegularPotential.volume_absolutelyContinuous_law (hV : KLS.RegularPotential V a b) :
    (volume : Measure E) ≪ (hV.law : Measure E) :=
  absolutelyContinuous_tilted hV.integrable_exp_neg
/-- A regular law has full support. -/
theorem FunctionalInequalities.KLS.RegularPotential.support_law (hV : KLS.RegularPotential V a b) :
    (hV.law : Measure E).support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  apply (Measure.mem_support_iff_forall x).2
  intro U hU
  have hmU : 0 < (volume : Measure E) U := Measure.measure_pos_of_mem_nhds volume hU
  exact pos_iff_ne_zero.2 fun h0 =>
    (pos_iff_ne_zero.1 hmU) (volume_absolutelyContinuous_law hV h0)
/-- Every regular law can be centered and whitened by an affine map preserving regularity: there is a
self-adjoint whitening `W` with the affine potential isotropic and its law the translated, whitened law. -/
theorem FunctionalInequalities.KLS.RegularPotential.exists_isotropic_comp_affine (hV : KLS.RegularPotential V a b) :
    ∃ W : E ≃L[ℝ] E,
      (W : E →L[ℝ] E).adjoint = W ∧
      (∀ u v, inner ℝ (Covariance.operator (hV.law : Measure E) (W u)) (W v) = inner ℝ u v) ∧
      KLS.Isotropic (comp_affine hV W.symm
        (∫ x, x ∂(hV.law : Measure E))).law ∧
      (comp_affine hV W.symm
        (∫ x, x ∂(hV.law : Measure E))).law =
          Probability.mapContinuousLinearEquiv
            (Probability.translateLaw hV.law (-∫ x, x ∂(hV.law : Measure E))) W := by
  obtain ⟨W, hWadj, hW⟩ := Covariance.exists_whitening (hV.law : Measure E)
    (fun _ hv => covariance_pos_408915f hV hv)
  refine ⟨W, hWadj, hW, isotropic_comp_affine_of_whitening_408915f hV W hWadj hW, ?_⟩
  simpa only [ContinuousLinearEquiv.symm_symm] using
    law_comp_affine_eq_map hV W.symm (∫ x, x ∂(hV.law : Measure E))
/-- **Regular laws reduce to isotropic regular laws** (BKL Section 2, p. 5, reduction of Theorem 1.1 to
isotropic regular laws): for every regular potential `V` there are an affine change of variables
`x ↦ W⁻¹ x + c` (`c` the mean, `W` a covariance whitening) and positive constants such that
`V (W⁻¹ · + c)` is regular and isotropic, with the explicit image law. -/
theorem FunctionalInequalities.KLS.RegularPotential.exists_regular_isotropic (hV : KLS.RegularPotential V a b) :
    ∃ (W : E ≃L[ℝ] E) (c : E) (V' : E → ℝ) (a' b' : ℝ)
      (hV' : KLS.RegularPotential V' a' b'),
      c = (∫ x, x ∂(hV.law : Measure E)) ∧
      V' = (fun x => V (W.symm x + c)) ∧
      a' = affineLowerConstant a W.symm ∧
      b' = affineUpperConstant b W.symm ∧
      0 < a' ∧ 0 < b' ∧ KLS.Isotropic hV'.law ∧
      hV'.law = Probability.mapContinuousLinearEquiv (Probability.translateLaw hV.law (-c)) W := by
  obtain ⟨W, _, _, hiso, hlaw⟩ := exists_isotropic_comp_affine hV
  refine ⟨W, _, _, _, _, comp_affine hV W.symm
    (∫ x, x ∂(hV.law : Measure E)), rfl, rfl, rfl, rfl, ?_, ?_, hiso, hlaw⟩
  · exact affineLowerConstant_pos hV.pos _
  · exact affineUpperConstant_pos _ _
end
end
end
end

section
open MeasureTheory Filter
open scoped Topology
noncomputable section
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private theorem FunctionalInequalities.KLS.RegularPotential.regular_ac {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b) :
    (hV.law : Measure E) ≪ volume :=
  hV.logConcave_law.absolutelyContinuous_of_interior_support_nonempty volume hV.interior_support_law
private theorem FunctionalInequalities.KLS.RegularPotential.regular_frontier {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b) :
    (hV.law : Measure E) (frontier (hV.law : Measure E).support) = 0 := by
  rw [support_law hV, frontier_univ, measure_empty]
private theorem FunctionalInequalities.KLS.RegularPotential.covariance_constant_eq_localSlope {V : E → ℝ} {a b : ℝ}
    (hV : KLS.RegularPotential V a b) (hiso : KLS.Isotropic hV.law) :
    Poincare.L2Energy.constant hV.law (Energy.CovarianceGradient.relaxation hV.law) =
      Poincare.LocalSlope.Intrinsic.constant hV.law := by
  rw [Energy.CovarianceGradient.relaxation_eq_lipschitz hV.law volume (regular_ac hV)
    (regular_frontier hV) hiso.covariance_identity,
    ← Poincare.SmoothTest.constant_eq_lipschitz_408915f hV.law volume (regular_ac hV) (regular_frontier hV)]
  exact hV.logConcave_law.smoothTest_constant_eq_localSlope
private theorem FunctionalInequalities.KLS.RegularPotential.localSlope_le_covariance_norm_of_covariance_constant {V : E → ℝ} {a b : ℝ}
    (hV : KLS.RegularPotential V a b) {K : NNReal}
    (hK : Poincare.L2Energy.constant hV.law (Energy.CovarianceGradient.relaxation hV.law) ≤ K) :
    Poincare.LocalSlope.Intrinsic.constant hV.law ≤
      (K : ENNReal) * ENNReal.ofReal ‖Covariance.operator (hV.law : Measure E)‖ := by
  have hlit : Poincare.LocalSlope.Intrinsic.constant hV.law =
      Poincare.L2Energy.constant hV.law
        (Energy.LipschitzGradient.relaxation hV.law volume (regular_ac hV)) := by
    rw [← hV.logConcave_law.smoothTest_constant_eq_localSlope,
      Poincare.SmoothTest.constant_eq_lipschitz_408915f hV.law volume (regular_ac hV) (regular_frontier hV)]
  have hh := (Poincare.L2Energy.holds_iff_constant_le hV.law
    (Energy.CovarianceGradient.relaxation hV.law) K).mpr hK
  have hcmp : ∀ f : (Energy.LipschitzGradient.relaxation hV.law volume (regular_ac hV)).domain,
      Energy.CovarianceGradient.relaxation hV.law f.1 ≤
        (‖Covariance.operator (hV.law : Measure E)‖₊ : ENNReal) *
          Energy.LipschitzGradient.relaxation hV.law volume (regular_ac hV) f.1 :=
    fun f => Energy.CovarianceGradient.relaxation_le_mul_lipschitz_408915f hV.law volume
      (regular_ac hV) (regular_frontier hV) f.1 ((Energy.Functional.mem_domain _ _).mp f.2)
  have h := Poincare.L2Energy.constant_le_mul_of_energy_le_mul hh hcmp
  rw [hlit]
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.coe_mul, mul_comm, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
/-- **Conditional Poincaré transfer** (BKL Section 2, p. 5): if every isotropic regular law (with positive
upper curvature) has literature constant `≤ K`, then every regular law has `C_P ≤ K·‖Cov‖` (center and
whiten by `exists_regular_isotropic`, then transport the covariance energy). The universal bound is a
hypothesis, not asserted. -/
theorem FunctionalInequalities.KLS.RegularPotential.localSlope_le_covariance_norm {K : NNReal}
    (hBound : ∀ {U : E → ℝ} {α β : ℝ} (hU : KLS.RegularPotential U α β),
      0 < β → KLS.Isotropic hU.law → Poincare.LocalSlope.Intrinsic.constant hU.law ≤ (K : ENNReal))
    {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b) :
    Poincare.LocalSlope.Intrinsic.constant hV.law ≤
      (K : ENNReal) * ENNReal.ofReal ‖Covariance.operator (hV.law : Measure E)‖ := by
  obtain ⟨W, c, U, α, β, hU, _, _, _, _, _, hβ, hiso, hlaw⟩ :=
    exists_regular_isotropic hV
  have hnew : Poincare.L2Energy.constant hU.law (Energy.CovarianceGradient.relaxation hU.law) ≤ (K : ENNReal) := by
    rw [covariance_constant_eq_localSlope hU hiso]
    exact hBound hU hβ hiso
  rw [hlaw, Poincare.CovarianceGradient.constant_mapContinuousLinearEquiv,
    Poincare.CovarianceGradient.constant_translateLaw] at hnew
  exact localSlope_le_covariance_norm_of_covariance_constant hV hnew
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `‖A‖ ≤ 1 + ‖A − Id‖`. -/
theorem FunctionalInequalities.KLS.RegularPotential.covariance_norm_le_envelope (A : E →L[ℝ] E) :
    ‖A‖ ≤ 1 + ‖A - ContinuousLinearMap.id ℝ E‖ := by
  calc
    ‖A‖ = ‖(A - ContinuousLinearMap.id ℝ E) + ContinuousLinearMap.id ℝ E‖ := by rw [sub_add_cancel]
    _ ≤ ‖A - ContinuousLinearMap.id ℝ E‖ + ‖ContinuousLinearMap.id ℝ E‖ := norm_add_le _ _
    _ ≤ 1 + ‖A - ContinuousLinearMap.id ℝ E‖ := by linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)]
/-- The transfer with the envelope coefficient `K (1 + ‖Cov − Id‖)`. -/
theorem FunctionalInequalities.KLS.RegularPotential.localSlope_le_covariance_envelope {K : NNReal}
    (hBound : ∀ {U : E → ℝ} {α β : ℝ} (hU : KLS.RegularPotential U α β),
      0 < β → KLS.Isotropic hU.law → Poincare.LocalSlope.Intrinsic.constant hU.law ≤ (K : ENNReal))
    {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b) :
    Poincare.LocalSlope.Intrinsic.constant hV.law ≤
      ENNReal.ofReal ((K : ℝ) * (1 + ‖Covariance.operator (hV.law : Measure E) - ContinuousLinearMap.id ℝ E‖)) := by
  have h := localSlope_le_covariance_norm hBound hV
  rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  apply h.trans
  gcongr
  exact covariance_norm_le_envelope _
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The envelope coefficient converges to `K` when the covariances converge to `Id`. -/
theorem FunctionalInequalities.KLS.RegularPotential.envelope_coefficient_tendsto {ι : Type*} {l : Filter ι} {A : ι → E →L[ℝ] E}
    (K : NNReal) (hA : Filter.Tendsto A l (𝓝 (ContinuousLinearMap.id ℝ E))) :
    Filter.Tendsto (fun i => (K : ℝ) * (1 + ‖A i - ContinuousLinearMap.id ℝ E‖)) l (𝓝 (K : ℝ)) := by
  have hnorm : Tendsto (fun i => ‖A i - ContinuousLinearMap.id ℝ E‖) l (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using
      (hA.sub (tendsto_const_nhds (x := ContinuousLinearMap.id ℝ E))).norm
  have hplus : Tendsto (fun i => 1 + ‖A i - ContinuousLinearMap.id ℝ E‖) l (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hnorm
  simpa only [mul_one] using (tendsto_const_nhds (x := (K : ℝ))).mul hplus
end
end
end
end
end

open MeasureTheory Filter Topology
noncomputable section
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
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- An isotropic law has full affine support (owner: `KLS/IsotropicSupport.lean`). -/
theorem FunctionalInequalities.KLS.LogConcave.affineSupport_eq_top_of_isotropic {μ : ProbabilityMeasure E} (hiso : KLS.Isotropic μ) :
    Probability.affineSupport μ = ⊤ :=
  hiso.affineSupport_eq_top
/-- An isotropic log-concave law has a Borell density with respect to Lebesgue measure. -/
theorem FunctionalInequalities.KLS.LogConcave.exists_isBorellDensity_of_isotropic {μ : ProbabilityMeasure E}
    (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ) :
    ∃ ρ : E → ℝ, KLS.IsBorellDensity (μ : Measure E) volume ρ := by
  have hi := hLC.interior_support_nonempty_of_affineSupport_eq_top (affineSupport_eq_top_of_isotropic hiso)
  exact hLC.exists_isBorellDensity_of_interior_support_nonempty volume hi
    (hLC.absolutelyContinuous_of_interior_support_nonempty volume hi)
/-- A literature Poincaré bound for a regular law is a smooth-test bound. -/
theorem FunctionalInequalities.KLS.LogConcave.RegularPotential.smoothTest_holds_of_localSlope_le {V : E → ℝ} {a b : ℝ}
    (hV : KLS.RegularPotential V a b) (C : NNReal)
    (hC : Poincare.LocalSlope.Intrinsic.constant hV.law ≤ (C : ENNReal)) :
    Poincare.SmoothTest.Holds (hV.law : Measure E) (C : ℝ) := by
  apply (Poincare.SmoothTest.holds_iff_ambient hV.law C).mpr
  apply (Poincare.SmoothGradient.Ambient.holds_iff_constant_le hV.law C).mpr
  rw [← Poincare.SmoothTest.constant_eq_ambient,
    hV.logConcave_law.smoothTest_constant_eq_localSlope]
  exact hC
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- **Reduction of the Poincaré bound to isotropic regular laws** (BKL Section 2, p. 5): if every
isotropic regular law on `E` (positive upper curvature) has literature constant `≤ K`, so does every
isotropic log-concave law on `E`: approximate by regular laws (`GaussianSmoothing.exists_regularSeq_limits`),
transfer the bound with the envelope coefficient `K(1+‖Cov−Id‖) → K`, and pass to the weak limit. -/
theorem solution {K : NNReal}
    (hBound : ∀ {V : E → ℝ} {a b : ℝ} (hV : FunctionalInequalities.KLS.RegularPotential V a b),
      0 < b → FunctionalInequalities.KLS.Isotropic hV.law →
        FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant hV.law ≤ (K : ENNReal))
    (μ : ProbabilityMeasure E) (hLC : FunctionalInequalities.KLS.LogConcave μ) (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant μ ≤ (K : ENNReal) := by
  by_cases hdim : Module.finrank ℝ E = 0
  · have : Subsingleton E := Module.finrank_zero_iff.mp hdim
    rw [FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_subsingleton]
    exact bot_le
  obtain ⟨ρ, hρ⟩ := FunctionalInequalities.KLS.LogConcave.exists_isBorellDensity_of_isotropic hLC hiso
  obtain ⟨k, _hkl, _hpos, _hδ, _hregular, _hb, hweak, _hmean, _hsecond, hcov⟩ :=
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_regularSeq_limits hρ hiso.memLp_two
  let ν : ℕ → ProbabilityMeasure E := fun n => FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.regularSeq hρ n (k n)
  let Cseq : ℕ → NNReal := fun n =>
    K * (1 + ‖FunctionalInequalities.Covariance.operator (ν n : Measure E) - ContinuousLinearMap.id ℝ E‖₊)
  have hcov' : Tendsto (fun n => FunctionalInequalities.Covariance.operator (ν n : Measure E)) atTop
      (𝓝 (ContinuousLinearMap.id ℝ E)) := by
    simpa only [ν, hiso.covariance_identity] using hcov
  have hC : Tendsto Cseq atTop (𝓝 K) := by
    apply NNReal.tendsto_coe.mp
    simpa only [Cseq, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, coe_nnnorm] using
      FunctionalInequalities.KLS.RegularPotential.envelope_coefficient_tendsto K hcov'
  apply FunctionalInequalities.KLS.LogConcave.localSlope_constant_le_of_tendsto_408915f ν μ hLC Cseq K hweak hC
  intro n
  have hV := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.regularPotential_quadraticPotential
    hρ (by positivity : (0 : ℝ) < (n : ℝ) + 1) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.tiltRate_pos (k n))
  have hlit := FunctionalInequalities.KLS.RegularPotential.localSlope_le_covariance_envelope hBound hV
  have hCeq : (Cseq n : ENNReal) =
      ENNReal.ofReal ((K : ℝ) *
        (1 + ‖FunctionalInequalities.Covariance.operator (hV.law : Measure E) - ContinuousLinearMap.id ℝ E‖)) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    rfl
  apply FunctionalInequalities.KLS.LogConcave.RegularPotential.smoothTest_holds_of_localSlope_le hV (Cseq n)
  rw [hCeq]
  exact hlit
