-- Prove2me | solution 1 for FunctionalInequalities.Analysis.actual_source_weak_trace_conservativity_data_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:39:46.832982+00:00
-- url     : https://prove2.me/submissions/d15aad59-f7ba-490c-961b-d193f7d53890

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Viscosity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_LinearEquiv
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Translation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Range
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Isotropic
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Stein_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
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
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Bases
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_hessianMatrixIn_posSemidef_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_ae_weak_third_derivative_symm_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_bounded_trace_quadratic_weak_derivative_data_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_regular_moment_bounded_weak_cutoff_testing_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_integrable_and_integral_eq_zero_of_cutoff_defect_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_integral_trace_quadratic_flux_eq_neg_density_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_trace_forcing_add_twice_energy_nonneg_408915f
import Theorems.Thm_FunctionalInequalities_Probability_Stein_norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f

section
noncomputable section
open MeasureTheory
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
/-- A unit normalisation `∫ e^{−φ} = 1` forces integrability of `e^{−φ}`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.integrable_exp_neg_of_integral_eq_one {α : Type*} [MeasurableSpace α] (m : Measure α)
    (φ : α → ℝ) (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) :
    Integrable (fun x => Real.exp (-φ x)) m := by
  by_contra hh
  rw [integral_undef hh] at hnorm
  norm_num at hnorm
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
end
end
end
end
end

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
noncomputable section HessianEntryBounds
open MeasureTheory
open FunctionalInequalities.Probability.Stein
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
namespace FunctionalInequalities.Probability.Stein
end FunctionalInequalities.Probability.Stein
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Stein
private lemma FunctionalInequalities.Probability.Stein.n10_hessian {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix u x = FunctionalInequalities.Probability.Stein.n10_matrix (fderiv ℝ (gradient u) x) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  have he : fderiv ℝ u = T ∘ gradient u :=
    funext fun y => (T.apply_symm_apply (fderiv ℝ u y)).symm
  have hd :
      fderiv ℝ (fderiv ℝ u) x =
        T.toContinuousLinearMap.comp (fderiv ℝ (gradient u) x) :=
    (congrArg (fun f => fderiv ℝ f x) he).trans T.comp_fderiv
  ext r s
  change
    fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin n) ℝ r)
        (EuclideanSpace.basisFun (Fin n) ℝ s) =
      T (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ r))
        (EuclideanSpace.basisFun (Fin n) ℝ s)
  rw [hd]
  rfl
private lemma FunctionalInequalities.Probability.Stein.n11b_continuous_hessian_entry {n : ℕ} (i j : Fin n) :
    Continuous
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        FunctionalInequalities.Probability.Stein.n10_matrix L i j) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  exact
    (T.continuous.comp (continuous_id.clm_apply continuous_const)).clm_apply
      continuous_const
/-- Measurability of the total coordinate Hessian, without smoothness premises. -/
theorem FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n) :
    Measurable (fun x => hessianMatrix u x i j) := by
  simpa only [n10_hessian, Function.comp_def] using
    (n11b_continuous_hessian_entry i j).measurable.comp
      (measurable_fderiv ℝ (gradient u))
end
end
end
end HessianEntryBounds
end

section RegularSource
open MeasureTheory Set
open scoped ContDiff
variable {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ)
noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein
section RegularMomentTraceQuadraticTesting
open MeasureTheory Set Filter Matrix
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
include hn hκ hK hKc hKint hW hstrong hμ hiso in
private theorem FunctionalInequalities.Analysis.actual_source_cutoff_trace_quadratic_testing :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ i j : Fin n,
      HasWeakDerivAlong
        (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              hessianMatrix u x i a *
                ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
    (let Q := fun x i j => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
  (    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ l k i j : Fin n,
      (∀ b : Fin n, Integrable (fun x => Real.exp (-u x) * J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
        fderiv ℝ W (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, ∃ C_B : ℝ, 0 ≤ C_B ∧
        (∀ x, ‖(B * hessianMatrix u x * B * hessianMatrix u x).trace‖ ≤ C_B) ∧
        LocallyIntegrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ k : Fin n,
          HasWeakDerivAlong (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
            (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
              2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ r : ℝ, 1 ≤ r →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨u, L, LF, T, hrest, c, C, hC, hlower, hreg, hmono, hpoint, hint, hbound, hdecay, hrough⟩ :=
    exists_regular_moment_bounded_weak_cutoff_testing_408915f hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hcopy := hrest
  rcases hcopy with ⟨_hc, _hl, _hnrm, _hm, _hC1, hG, _hF, _hw, _hd, hT, _he,
    _hfirst, _hInv, _hmean, _hq, _hflux, _hweighted, _hbounded⟩
  refine ⟨u, L, LF, T, hrest, c, C, hC, hlower, hreg, hmono, hpoint, hint, hbound, hdecay, ?_⟩
  dsimp only
  intro B
  obtain ⟨C_B, hCB, hfbound, hfloc, hweakB⟩ := bounded_trace_quadratic_weak_derivative_data_408915f
    B (fun x => hessianMatrix u x) (fun k x => Matrix.of fun i j => T x k i j)
    (fun i j => measurable_hessianMatrix_entry u i j)
    (fun x i j => norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f hG x i j)
    (fun k i j => (hT k i j).1) (fun k i j => (hT k i j).2)
  refine ⟨C_B, hCB, hfbound, hfloc, hweakB, ?_⟩
  intro r hr
  exact hrough r hr _ _ C_B hfloc hfbound
    (fun k => (hweakB k).1) (fun k => (hweakB k).2)
end
end
end RegularMomentTraceQuadraticTesting
section RegularMomentWeakTraceContraction
open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
include hn hκ hK hKc hKint hW hstrong hμ hiso in
private theorem FunctionalInequalities.Analysis.actual_source_weak_trace_contraction_data :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ((ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ i j : Fin n,
      HasWeakDerivAlong
        (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              hessianMatrix u x i a *
                ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
    (let Q := fun x i j => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
  (    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ l k i j : Fin n,
      (∀ b : Fin n, Integrable (fun x => Real.exp (-u x) * J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * hessianMatrix u x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * (ψ x * hessianMatrix u x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
        fderiv ℝ W (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, ∃ C_B : ℝ, 0 ≤ C_B ∧
        (∀ x, ‖(B * hessianMatrix u x * B * hessianMatrix u x).trace‖ ≤ C_B) ∧
        LocallyIntegrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ k : Fin n,
          HasWeakDerivAlong (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
            (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
              2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ r : ℝ, 1 ≤ r →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace * Lχ r x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (2 * (B * hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ,
      let H := fun x => hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let a := fun x i => 2 * (B * H x * B * Tm x i).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        Integrable (fun x => Real.exp (-u x) * g x * ψ x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ j : Fin n, Integrable (fun x => Real.exp (-u x) *
          (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (∫ x, Real.exp (-u x) * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨u, L, LF, T, hOld⟩ := actual_source_cutoff_trace_quadratic_testing
    hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hcopy := hOld
  rcases hcopy with ⟨hbase, _hcutoffs⟩
  rcases hbase with ⟨_hc, _hl, _hnrm, _hm, hC1, hG, _hF, _hw, _hd, hT, _he,
    _hfirst, _hInv, _hmean, _hq, _hflux, hweighted, hbounded⟩
  refine ⟨u, L, LF, T, hOld, ?_⟩
  intro B
  apply integral_trace_quadratic_flux_eq_neg_density_408915f B
    (fun x => hessianMatrix u x) (fun x => (hessianMatrix u x)⁻¹)
    (fun x => Matrix.of fun i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b) * (hessianMatrix u x)⁻¹ *
        (Matrix.of fun a b => T x j a b)).trace)
    (fun x i => Matrix.of fun a b => T x i a b) (fun x => Real.exp (-u x))
    (Real.continuous_exp.comp hC1.continuous.neg)
  · intro i j
    exact memLp_top_of_bound (measurable_hessianMatrix_entry u i j).aestronglyMeasurable
      (Real.toNNReal (16 / κ) : ℝ) (Filter.Eventually.of_forall fun x =>
        norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f hG x i j)
  · exact fun a i j => (hT a i j).2
  · exact fun i j a => (hweighted i j).1 a
  · exact fun i j => (hweighted i j).2.1
  · exact fun ψ hψ hψc l k i j => (hbounded ψ hψ hψc l k i j).2.2
end
end
end RegularMomentWeakTraceContraction
section RegularMomentWeakTraceDensity
open MeasureTheory Set Matrix
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
private theorem FunctionalInequalities.Analysis.ae_weak_trace_density_add_twice_energy_nonneg {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k)) :
    let E := fun x => Matrix.of fun i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b) *
        (hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x j a b)).trace
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      0 ≤ (2 * (B * hessianMatrix u x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
          (B * (Matrix.of fun a b => T x i a b) * B *
            (Matrix.of fun a b => T x j a b)).trace) +
        2 * (B * hessianMatrix u x * B * hessianMatrix u x).trace := by
  have hW2 : ContDiff ℝ 2 W := hW.of_le (WithTop.coe_le_coe.mpr le_top)
  have hVc : ConvexOn ℝ univ W := by
    have hn' : ConvexOn ℝ univ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) :=
      convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
    have hq := hn'.smul (show 0 ≤ κ / 2 by positivity)
    have he :
        (fun y => W y - κ / 2 * ‖y‖ ^ 2) +
          (fun y => (κ / 2) • ‖y‖ ^ 2) = W := by
      funext y
      simp only [Pi.add_apply, smul_eq_mul, sub_add_cancel]
    rw [← he]
    exact hstrong.add hq
  have hWP (x : EuclideanSpace ℝ (Fin n)) : (hessianMatrix W x).PosSemidef :=
    hessianMatrixIn_posSemidef_408915f (EuclideanSpace.basisFun (Fin n) ℝ) hW2.contDiffAt
      (bilinearIteratedFDerivTwo_nonneg_of_convexOn hW2 hVc x)
  have hsym := ae_weak_third_derivative_symm_408915f hu hG hT
  dsimp only
  filter_upwards [hPD, hsym] with x hPx hSx
  intro B hB
  have hTx : ∀ i : Fin n, (Matrix.of fun a b => T x i a b).IsSymm := by
    intro i
    ext a b
    exact (hSx i b a).2
  exact trace_forcing_add_twice_energy_nonneg_408915f B (hessianMatrix u x)
    (hessianMatrix u x)⁻¹ (hessianMatrix W (gradient u x)) hB hPx.posSemidef
    hPx.inv.posSemidef (hWP _) (fun i => Matrix.of fun a b => T x i a b) hTx
end
end
end RegularMomentWeakTraceDensity
section RegularMomentTiltedCutoffConservativity
open MeasureTheory Filter
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
private theorem FunctionalInequalities.Analysis.integrable_zero_tilted_of_weighted_cutoff_defect {n : ℕ}
    (u f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hnorm : (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hf : LocallyIntegrable f (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg : LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C)
    (c : ℝ) (hc : 0 < c)
    (hLower : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ g x + c * f x)
    (chi defect : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hChi : ∀ m, Continuous (chi m))
    (hChiBounds : ∀ m x, 0 ≤ chi m x ∧ chi m x ≤ 1)
    (hChiLim : ∀ x, Tendsto (fun m => chi m x) atTop (𝓝 1))
    (hDefect : ∀ m, Integrable (defect m)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)))
    (hDefectLim : Tendsto (fun m => ∫ x, |defect m x|
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0))
    (hCutoff : ∀ m, Integrable (fun x => chi m x * g x * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hPair : ∀ m,
      (∫ x, chi m x * g x * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, f x * defect m x * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Integrable g ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
      (∫ x, g x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) = 0 := by
  have hexp := BakryEmery.integrable_exp_neg_of_integral_eq_one
    (volume : Measure (EuclideanSpace ℝ (Fin n))) u hnorm
  let nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
    ⟨(volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u), isProbabilityMeasure_tilted hexp⟩
  have hac := tilted_absolutelyContinuous
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (-u)
  apply integrable_and_integral_eq_zero_of_cutoff_defect_408915f nu f g
    (hf.aestronglyMeasurable.mono_ac hac) (hg.aestronglyMeasurable.mono_ac hac)
    C hC (Filter.Eventually.of_forall hbound) c hc (hac.ae_le hLower) chi defect
    (fun m => (hChi m).aestronglyMeasurable)
    (fun m => Filter.Eventually.of_forall (hChiBounds m))
    (Filter.Eventually.of_forall hChiLim) hDefect hDefectLim
  · intro m
    apply (integrable_tilted_iff hexp _).mpr
    simpa only [Pi.neg_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hCutoff m
  · intro m
    change (∫ x, chi m x * g x
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
      ∫ x, f x * defect m x
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))
    rw [integral_tilted, integral_tilted]
    simp only [Pi.neg_apply, hnorm, div_one, smul_eq_mul]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hPair m
end
end
end RegularMomentTiltedCutoffConservativity
section RegularMomentWeakTraceConservativity
open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
include hn hκ hK hKc hKint hW hstrong hμ hiso in
set_option maxHeartbeats 800000 in
 theorem solution :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (      ((ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef ∧
        Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det)
          (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det *
            ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det *
            ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det)
          (fun x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j)
          (fun x => -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ i j : Fin n,
        Integrable (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, FunctionalInequalities.Probability.Stein.hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ i j : Fin n,
      FunctionalInequalities.Analysis.HasWeakDerivAlong
        (fun x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => -FunctionalInequalities.Probability.Stein.hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
              ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -FunctionalInequalities.Probability.Stein.hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
                ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
    (let Q := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
              ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a)
    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
  (    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x i j +
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x i j +
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ l k i j : Fin n,
      (∀ b : Fin n, Integrable (fun x => Real.exp (-u x) * J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * (ψ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * (ψ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix (χ R) x).trace -
        fderiv ℝ W (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, ∃ C_B : ℝ, 0 ≤ C_B ∧
        (∀ x, ‖(B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * FunctionalInequalities.Probability.Stein.hessianMatrix u x).trace‖ ≤ C_B) ∧
        LocallyIntegrable (fun x => (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * FunctionalInequalities.Probability.Stein.hessianMatrix u x).trace)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ k : Fin n,
          FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * FunctionalInequalities.Probability.Stein.hessianMatrix u x).trace)
            (fun x => 2 * (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => 2 * (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
              2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ r : ℝ, 1 ≤ r →
        Integrable (fun x => (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * FunctionalInequalities.Probability.Stein.hessianMatrix u x).trace * Lχ r x * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
          (2 * (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * FunctionalInequalities.Probability.Stein.hessianMatrix u x).trace * Lχ r x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
          (2 * (B * FunctionalInequalities.Probability.Stein.hessianMatrix u x * B * (Matrix.of fun a b => T x i a b)).trace) *
          fderiv ℝ (χ r) x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ,
      let H := fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let a := fun x i => 2 * (B * H x * B * Tm x i).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        Integrable (fun x => Real.exp (-u x) * g x * ψ x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∀ j : Fin n, Integrable (fun x => Real.exp (-u x) *
          (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (∫ x, Real.exp (-u x) * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
      let H := fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x
      let R := fun x => (H x)⁻¹
      let Tm := fun x i => Matrix.of fun a b => T x i a b
      let E := fun x => Matrix.of fun i j => -H x i j +
        (H x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * H x) i j +
        (R x * Tm x i * R x * Tm x j).trace
      let g := fun x => 2 * (B * H x * B * E x).trace +
        2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
      Integrable g ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, g x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) = 0 := by
  obtain ⟨u, L, LF, T, hOld, hTrace⟩ := actual_source_weak_trace_contraction_data
    hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hcopy := hOld
  rcases hcopy with ⟨hbase, hcutoffs⟩
  rcases hbase with ⟨_hc, _hl, hnrm, _hm, hC1, hG, _hF, _hw, hdata, hT, _he,
    _hfirst, _hInv, _hmean, _hq, _hflux, _hweighted, _hbounded⟩
  obtain ⟨c, C, _hC, _hlower, hreg, _hmono, hpoint, hint, _hbound, hdecay, hrough⟩ := hcutoffs
  refine ⟨u, L, LF, T, ⟨hOld, hTrace⟩, ?_⟩
  intro B hB
  dsimp only
  let H := fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x
  let R := fun x => (H x)⁻¹
  let Tm := fun x i => Matrix.of fun a b => T x i a b
  let E := fun x => Matrix.of fun i j => -H x i j +
    (H x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * H x) i j +
    (R x * Tm x i * R x * Tm x j).trace
  let a := fun x i => 2 * (B * H x * B * Tm x i).trace
  let g := fun x => 2 * (B * H x * B * E x).trace +
    2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * Tm x i * B * Tm x j).trace
  let f := fun x => (B * H x * B * H x).trace
  let chi := fun (r : ℝ) x => Real.smoothTransition (2 - (u x - c) / r)
  let defect := fun (r : ℝ) x => ((H x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix (chi r) x).trace -
    fderiv ℝ W (gradient u x) (gradient (chi r) x)
  have h1 (m : ℕ) : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hcofinal : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  obtain ⟨C_B, hCB, hfbound, hfloc, _hweakB, hpair⟩ := hrough B
  have hTr := hTrace B
  have hLower : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      0 ≤ g x + 2 * f x := by
    have hn := ae_weak_trace_density_add_twice_energy_nonneg hκ hW hstrong hC1 hG
      (hdata.mono fun _ hx => hx.1) T (fun k i j => (hT k i j).1)
    filter_upwards [hn] with x hx
    exact hx B hB
  apply integrable_zero_tilted_of_weighted_cutoff_defect u f g hnrm hfloc hTr.1
    C_B hCB (fun x => by simpa only [Real.norm_eq_abs] using hfbound x)
    2 (by norm_num) hLower
    (fun m => chi ((m : ℝ) + 1)) (fun m => defect ((m : ℝ) + 1))
    (fun m => (hreg _ (h1 m)).1.continuous)
    (fun m => (hreg _ (h1 m)).2.2.2)
    (fun x => (hpoint x).comp hcofinal)
    (fun m => hint _ (h1 m)) (hdecay.comp hcofinal)
  · intro m
    have ht := (hTr.2 (chi ((m : ℝ) + 1)) (hreg _ (h1 m)).1
      (hreg _ (h1 m)).2.1).1
    change Integrable (fun x => Real.exp (-u x) * g x * chi ((m : ℝ) + 1) x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) at ht
    apply ht.congr
    filter_upwards [] with x
    ring
  · intro m
    have ht := (hTr.2 (chi ((m : ℝ) + 1)) (hreg _ (h1 m)).1
      (hreg _ (h1 m)).2.1).2.2
    have hp := (hpair ((m : ℝ) + 1) (h1 m)).2.2
    have hswap :
        (∫ x, (∑ i : Fin n, ∑ j : Fin n, R x i j * a x i *
          fderiv ℝ (chi ((m : ℝ) + 1)) x (EuclideanSpace.basisFun (Fin n) ℝ j)) *
          Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, Real.exp (-u x) * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
          fderiv ℝ (chi ((m : ℝ) + 1)) x (EuclideanSpace.basisFun (Fin n) ℝ j))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [mul_comm, Finset.sum_comm]
      simp only [Finset.sum_mul]
    change (∫ x, f x * defect ((m : ℝ) + 1) x * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = _ at hp
    rw [hswap, ht] at hp
    have heq : (∫ x, Real.exp (-u x) * g x * chi ((m : ℝ) + 1) x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, chi ((m : ℝ) + 1) x * g x * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    rw [heq, neg_neg] at hp
    exact hp.symm
