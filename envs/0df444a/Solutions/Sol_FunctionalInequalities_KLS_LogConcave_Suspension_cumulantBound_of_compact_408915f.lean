-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBound_of_compact_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:25:52.087759+00:00
-- url     : https://prove2.me/submissions/a711866d-9f83-4040-95c2-30e2f1850e20

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_CompactReduction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Law
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Translation
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Statement
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
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
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
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
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_map_affine_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_two_eq_centered_moment_of_integrable_exp_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_memLp_of_polynomial_bound_of_integrable_exp_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tendsto_cumulant_cond_closedBall_408915f
import Theorems.Thm_FunctionalInequalities_KLS_BorelLogConcave_exists_integrable_exp_norm_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_exists_standardized_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_inner_self_pos_of_norm_sub_one_lt_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_norm_sub_one_le_of_isPositive_mul_self_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_opNorm_le_of_inner_eq_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_cond_408915f

section
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- A strictly positive operator (`⟪T v, v⟫ > 0` for `v ≠ 0`) on a finite-dimensional space is a unit. -/
theorem FunctionalInequalities.Analysis.isUnit_of_inner_self_pos (T : E →L[ℝ] E)
    (hpos : ∀ v : E, v ≠ 0 → 0 < ⟪T v, v⟫) : IsUnit T := by
  apply ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr
  apply (LinearMap.isUnit_iff_ker_eq_bot T.toLinearMap).mpr
  apply bot_unique
  intro v hv
  have hv' : T v = 0 := hv
  change v = 0
  by_contra hne
  have hp := hpos v hne
  rw [hv', inner_zero_left] at hp
  exact (lt_irrefl 0) hp
end FiniteDimensional
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
/-- The covariance operator is self-adjoint. -/
theorem FunctionalInequalities.Covariance.operator_isSelfAdjoint (μ : Measure E) : IsSelfAdjoint (Covariance.operator μ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪Covariance.operator μ x, y⟫ = ⟪x, Covariance.operator μ y⟫
  calc
    ⟪Covariance.operator μ x, y⟫ = covarianceBilin μ x y := Covariance.operator_inner μ x y
    _ = covarianceBilin μ y x := covarianceBilin_comm x y
    _ = ⟪Covariance.operator μ y, x⟫ := (Covariance.operator_inner μ y x).symm
    _ = ⟪x, Covariance.operator μ y⟫ := real_inner_comm _ _
end
end

section
noncomputable section
open scoped RealInnerProductSpace MatrixOrder
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section OperatorMatrix
open Matrix
variable [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_operatorOfMatrix (b : OrthonormalBasis ι ℝ E) (M : Matrix ι ι ℝ) :
    operatorMatrix b (operatorOfMatrix b M) = M := by
  exact (LinearMap.toMatrixOrthonormal b).apply_symm_apply M
@[simp] theorem FunctionalInequalities.Analysis.operatorOfMatrix_operatorMatrix (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    operatorOfMatrix b (operatorMatrix b T) = T := by
  exact congrArg (fun f : E →ₗ[ℝ] E => f.toContinuousLinearMap)
    ((LinearMap.toMatrixOrthonormal b).symm_apply_apply T.toLinearMap)
theorem FunctionalInequalities.Analysis.operatorMatrix_injective (b : OrthonormalBasis ι ℝ E) : Function.Injective (operatorMatrix b) := by
  intro S T h
  have := congrArg (operatorOfMatrix b) h
  simpa only [operatorOfMatrix_operatorMatrix] using this
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_mul (b : OrthonormalBasis ι ℝ E) (S T : E →L[ℝ] E) :
    operatorMatrix b (S * T) = operatorMatrix b S * operatorMatrix b T := by
  exact map_mul (LinearMap.toMatrixOrthonormal b) S.toLinearMap T.toLinearMap
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_one (b : OrthonormalBasis ι ℝ E) :
    operatorMatrix b (1 : E →L[ℝ] E) = 1 := by
  exact map_one (LinearMap.toMatrixOrthonormal b)
/-- The matrix is positive semidefinite iff the operator is positive (Mathlib `posSemidef_toMatrix_iff`). -/
theorem FunctionalInequalities.Analysis.operatorMatrix_posSemidef_iff (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    (operatorMatrix b T).PosSemidef ↔ T.IsPositive :=
  LinearMap.posSemidef_toMatrix_iff b
theorem FunctionalInequalities.Analysis.operatorOfMatrix_isPositive (b : OrthonormalBasis ι ℝ E) (M : Matrix ι ι ℝ)
    (hM : M.PosSemidef) : (operatorOfMatrix b M).IsPositive := by
  apply (operatorMatrix_posSemidef_iff b _).mp
  simpa only [operatorMatrix_operatorOfMatrix] using hM
/-- The matrix inverse of a unit's matrix is the matrix of `Ring.inverse`. -/
theorem FunctionalInequalities.Analysis.operatorMatrix_ringInverse (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) (hA : IsUnit A) :
    (operatorMatrix b A)⁻¹ = operatorMatrix b (Ring.inverse A) := by
  apply Matrix.inv_eq_right_inv
  rw [← operatorMatrix_mul, Ring.mul_inverse_cancel A hA, operatorMatrix_one]
end OperatorMatrix
end
end
end
end

section
noncomputable section
open scoped MatrixOrder RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_inverseSqrtIn (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    operatorMatrix b (inverseSqrtIn b A) = CFC.sqrt ((operatorMatrix b A)⁻¹) :=
  operatorMatrix_operatorOfMatrix b _
theorem FunctionalInequalities.Analysis.inverseSqrtIn_isPositive (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    (inverseSqrtIn b A).IsPositive :=
  operatorOfMatrix_isPositive b _ (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _))
theorem FunctionalInequalities.Analysis.inverseSqrtIn_isSelfAdjoint (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    IsSelfAdjoint (inverseSqrtIn b A) := (inverseSqrtIn_isPositive b A).isSelfAdjoint
/-- `σ² = Ring.inverse A` for a positive unit `A`. -/
theorem FunctionalInequalities.Analysis.inverseSqrtIn_mul_self (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) :
    inverseSqrtIn b A * inverseSqrtIn b A = Ring.inverse A := by
  apply operatorMatrix_injective b
  rw [operatorMatrix_mul]
  rw [operatorMatrix_inverseSqrtIn]
  rw [CFC.sqrt_mul_sqrt_self _ ((operatorMatrix_posSemidef_iff b A).mpr hpos).inv.nonneg,
    operatorMatrix_ringInverse b A hunit]
/-- `σ σ* = Ring.inverse A`. -/
theorem FunctionalInequalities.Analysis.inverseSqrtIn_mul_adjoint (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) :
    inverseSqrtIn b A * (inverseSqrtIn b A).adjoint = Ring.inverse A := by
  have hsa : (inverseSqrtIn b A).adjoint = inverseSqrtIn b A :=
    inverseSqrtIn_isSelfAdjoint b A
  rw [hsa]
  exact inverseSqrtIn_mul_self b A hpos hunit
/-- `A σσ* = 1 = σσ* A`. -/
theorem FunctionalInequalities.Analysis.inverseSqrtIn_mul_adjoint_cancel (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) :
    A * (inverseSqrtIn b A * (inverseSqrtIn b A).adjoint) = 1 ∧
      (inverseSqrtIn b A * (inverseSqrtIn b A).adjoint) * A = 1 := by
  rw [inverseSqrtIn_mul_adjoint b A hpos hunit]
  exact ⟨Ring.mul_inverse_cancel A hunit, Ring.inverse_mul_cancel A hunit⟩
/-- **Specification of `A^{-1/2}`** for a positive unit `A`: positive, self-adjoint, `σ² = σσ* = Ring.inverse A`,
`A σσ* = σσ* A = 1`. -/
theorem FunctionalInequalities.Analysis.inverseSqrt_spec (A : E →L[ℝ] E) (hpos : A.IsPositive) (hunit : IsUnit A) :
    (inverseSqrt A).IsPositive ∧ IsSelfAdjoint (inverseSqrt A) ∧
      inverseSqrt A * inverseSqrt A = Ring.inverse A ∧
      inverseSqrt A * (inverseSqrt A).adjoint = Ring.inverse A ∧
      A * (inverseSqrt A * (inverseSqrt A).adjoint) = 1 ∧
      (inverseSqrt A * (inverseSqrt A).adjoint) * A = 1 := by
  exact ⟨inverseSqrtIn_isPositive _ A, inverseSqrtIn_isSelfAdjoint _ A,
    inverseSqrtIn_mul_self _ A hpos hunit, inverseSqrtIn_mul_adjoint _ A hpos hunit,
    inverseSqrtIn_mul_adjoint_cancel _ A hpos hunit⟩
end
end
end
end

section
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section SecondCumulant
/-- One exponential moment gives `id ∈ L²(μ)`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.memLp_id_two_of_integrable_exp (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    MemLp id 2 μ := by
  have hn : MemLp (fun x : E => ‖x‖) 2 μ := by
    apply memLp_of_polynomial_bound_of_integrable_exp_408915f μ hr hexp continuous_norm (C := 1) (k := 1)
    intro x
    simp only [norm_norm, pow_one, one_mul]
    linarith
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
  exact (memLp_two_iff_integrable_sq hn.aestronglyMeasurable).1 hn
/-- The second cumulant is the covariance pairing `⟪Cov(μ) u, v⟫`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.cumulant_two_eq_covariance_of_integrable_exp (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (u v : E) :
    cumulant μ 2 ![u, v] = ⟪Covariance.operator μ u, v⟫ := by
  have h2 := memLp_id_two_of_integrable_exp μ hr hexp
  have hX : MemLp (fun x => ⟪u, x⟫) 2 μ := by
    simpa only [id_eq] using h2.const_inner (𝕜 := ℝ) u
  have hY : MemLp (fun x => ⟪v, x⟫) 2 μ := by
    simpa only [id_eq] using h2.const_inner (𝕜 := ℝ) v
  rw [Covariance.operator_inner, ProbabilityTheory.covarianceBilin_apply_eq_cov h2,
    ProbabilityTheory.covariance_eq_sub hX hY]
  exact cumulant_two_eq_centered_moment_of_integrable_exp_408915f μ hr hexp u v
end SecondCumulant
end
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
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
section CondHelpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem FunctionalInequalities.Analysis.BakryEmery.eventually_measure_closedBall_ne_zero_cond (ν : Measure E) [IsProbabilityMeasure ν] :
    ∀ᶠ R : ℕ in atTop, ν (Metric.closedBall (0 : E) R) ≠ 0 := by
  have hmono : Monotone fun R : ℕ => Metric.closedBall (0 : E) (R : ℝ) := fun m n hmn =>
    Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
  have hB : Tendsto (fun R : ℕ => ν (Metric.closedBall (0 : E) R)) atTop (𝓝 1) := by
    have := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rwa [Metric.iUnion_closedBall_nat, measure_univ] at this
  filter_upwards [hB.eventually (lt_mem_nhds (zero_lt_one' ENNReal))] with R hR
  exact hR.ne'
end CondHelpers
end
end
end
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
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
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.Suspension
section S8CCompactToGeneral
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
open Filter Topology ProbabilityTheory FunctionalInequalities.Analysis
section OperatorHelpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Inverse square roots of operators converging to `1` converge to `1`. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.tendsto_inverseSqrt_one
    [CompleteSpace E]
    [FiniteDimensional ℝ E] {Sg : ℕ → E →L[ℝ] E}
    (hSg : Tendsto Sg atTop (𝓝 1))
    (hpos : ∀ᶠ R in atTop, (Sg R).IsPositive) (hunit : ∀ᶠ R in atTop, IsUnit (Sg R)) :
    Tendsto (fun R => inverseSqrt (Sg R)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun R => Ring.inverse (Sg R)) atTop (𝓝 1) := by
    have := (NormedRing.inverse_continuousAt (1 : (E →L[ℝ] E)ˣ)).tendsto.comp hSg
    simpa [Function.comp_def] using this
  rw [tendsto_iff_norm_sub_tendsto_zero] at hinv ⊢
  refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ hinv
  filter_upwards [hpos, hunit] with R hp hu
  exact norm_sub_one_le_of_isPositive_mul_self_408915f (inverseSqrt_spec _ hp hu).1
    (inverseSqrt_spec _ hp hu).2.2.1
end OperatorHelpers
section MeasureHelpers
variable {E : Type*} [NormedAddCommGroup E]
section InnerProduct
variable [InnerProductSpace ℝ E]
/-- A ball truncation has exponential moments of every order. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.integrable_exp_cond_closedBall [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] (R : ℕ)
    (hR : ν (Metric.closedBall (0 : E) R) ≠ 0) (t : ℝ) :
    Integrable (fun x => Real.exp (t * ‖x‖)) (ν[|Metric.closedBall (0 : E) R]) := by
  have hres : Integrable (fun x => Real.exp (t * ‖x‖)) (ν.restrict (Metric.closedBall (0 : E) R)) := by
    refine (integrable_const (Real.exp (|t| * R))).mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    have hx' : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
    calc
      t * ‖x‖ ≤ |t| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self t) (norm_nonneg x)
      _ ≤ |t| * R := mul_le_mul_of_nonneg_left hx' (abs_nonneg t)
  exact hres.smul_measure (ENNReal.inv_ne_top.2 hR)
/-- A ball truncation is compactly supported. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.isCompact_support_cond_closedBall [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) (R : ℕ) :
    IsCompact (ν[|Metric.closedBall (0 : E) R]).support := by
  refine (isCompact_closedBall (0 : E) R).of_isClosed_subset Measure.isClosed_support
    (Measure.support_subset_of_isClosed Metric.isClosed_closedBall ?_)
  rw [mem_ae_iff, cond_apply Metric.isClosed_closedBall.measurableSet]
  simp
end InnerProduct
end MeasureHelpers
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension in
/-- **Reduction to compactly supported laws** (BKL arXiv:2610.05474v1, p. 19 and the end of Section 6, "standard
approximation argument"): a cumulant bound for compactly supported isotropic log-concave laws holds for all isotropic
log-concave laws, for every order `d + 1 ≥ 2`. -/
theorem solution {d : ℕ} (hd : 1 ≤ d) {b : ℝ} (h : FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBoundCompact d b) :
    FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBound d b := by
  classical
  intro m ν hiso hLC u
  obtain ⟨r, hr, hexp⟩ := ((FunctionalInequalities.KLS.LogConcave.borel_iff ν).1 hLC).exists_integrable_exp_norm_408915f
  let E := EuclideanSpace ℝ (Fin m)
  let νR : ℕ → Measure E := fun R => (ν : Measure E)[|Metric.closedBall (0 : E) R]
  let Sg : ℕ → E →L[ℝ] E := fun R => FunctionalInequalities.Covariance.operator (νR R)
  let T : ℕ → E →L[ℝ] E := fun R => FunctionalInequalities.Analysis.inverseSqrt (Sg R)
  have hmass : ∀ᶠ R : ℕ in atTop, (ν : Measure E) (Metric.closedBall (0 : E) R) ≠ 0 :=
    FunctionalInequalities.Analysis.BakryEmery.eventually_measure_closedBall_ne_zero_cond (ν : Measure E)
  have hcum2 := FunctionalInequalities.Analysis.BakryEmery.tendsto_cumulant_cond_closedBall_408915f (ν : Measure E) hr hexp 2
  have hcumd := FunctionalInequalities.Analysis.BakryEmery.tendsto_cumulant_cond_closedBall_408915f (ν : Measure E) hr hexp (d + 1)
  have hSg : Tendsto Sg atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    rw [tendsto_iff_norm_sub_tendsto_zero] at hcum2
    refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ hcum2
    filter_upwards [hmass] with R hR
    have : IsProbabilityMeasure (νR R) := cond_isProbabilityMeasure hR
    have hexpR : Integrable (fun x => Real.exp (r * ‖x‖)) (νR R) :=
      (hexp.restrict (s := Metric.closedBall (0 : E) R)).smul_measure (ENNReal.inv_ne_top.2 hR)
    refine FunctionalInequalities.KLS.LogConcave.Suspension.opNorm_le_of_inner_eq_408915f fun v w => ?_
    simp only [sub_apply]
    rw [FunctionalInequalities.Analysis.BakryEmery.cumulant_two_eq_covariance_of_integrable_exp
        ((ν : Measure E)[|Metric.closedBall (0 : E) R]) hr hexpR v w,
      FunctionalInequalities.Analysis.BakryEmery.cumulant_two_eq_covariance_of_integrable_exp (ν : Measure E) hr hexp v w,
      hiso.covariance_identity]
    simp [Sg, νR, inner_sub_left]
  have hpos : ∀ R, (Sg R).IsPositive := fun R =>
    (ContinuousLinearMap.isPositive_iff' _).mpr
      ⟨FunctionalInequalities.Covariance.operator_isSelfAdjoint _, fun v => by
        rw [FunctionalInequalities.Covariance.operator_inner]; exact ProbabilityTheory.covarianceBilin_self_nonneg v⟩
  have hlt : ∀ᶠ R in atTop, ‖Sg R - 1‖ < 1 :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hSg).eventually (gt_mem_nhds one_pos)
  have hunit : ∀ᶠ R in atTop, IsUnit (Sg R) := hlt.mono fun R hR =>
    FunctionalInequalities.Analysis.isUnit_of_inner_self_pos _ fun v hv => FunctionalInequalities.KLS.LogConcave.Suspension.inner_self_pos_of_norm_sub_one_lt_408915f hR hv
  have hT : Tendsto T atTop (𝓝 1) := FunctionalInequalities.KLS.LogConcave.Suspension.tendsto_inverseSqrt_one hSg (Eventually.of_forall hpos) hunit
  have hbound : ∀ᶠ R in atTop, ∑ J : Fin d → Fin m, FunctionalInequalities.Analysis.BakryEmery.cumulant (νR R) (d + 1)
      (Fin.cons (T R u) fun k => T R (EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2 ≤ b * ‖u‖ ^ 2 := by
    filter_upwards [hmass, hunit] with R hR hu
    have : IsProbabilityMeasure (νR R) := cond_isProbabilityMeasure hR
    let μR : ProbabilityMeasure E := ⟨νR R, inferInstance⟩
    have hLCR : FunctionalInequalities.KLS.LogConcave μR := hLC.cond_408915f (convex_closedBall _ _) Metric.isClosed_closedBall hR
    have hcR : IsCompact (μR : Measure E).support := FunctionalInequalities.KLS.LogConcave.Suspension.isCompact_support_cond_closedBall (ν : Measure E) R
    obtain ⟨η, W, hW, hiso', hLC', hc', hmap⟩ := FunctionalInequalities.KLS.LogConcave.Suspension.exists_standardized_408915f μR hLCR hcR (hpos R) hu
    have hb := h m η hiso' hLC' hc' u
    have hexpR : ∀ t : ℝ, Integrable (fun x => Real.exp (t * ‖x‖)) (νR R) :=
      FunctionalInequalities.KLS.LogConcave.Suspension.integrable_exp_cond_closedBall (ν : Measure E) R hR
    have hk : 2 ≤ d + 1 := by omega
    have hself : (FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator (μR : Measure E))).adjoint =
        FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator (μR : Measure E)) :=
      (FunctionalInequalities.Analysis.inverseSqrt_spec _ (hpos R) hu).2.1.adjoint_eq
    calc
      ∑ J : Fin d → Fin m, FunctionalInequalities.Analysis.BakryEmery.cumulant (νR R) (d + 1)
          (Fin.cons (T R u) fun k => T R (EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2
          = ∑ J : Fin d → Fin m, FunctionalInequalities.Analysis.BakryEmery.cumulant (η : Measure E) (d + 1)
            (Fin.cons u fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k)) ^ 2 := by
        refine Finset.sum_congr rfl fun J _ => ?_
        congr 1
        rw [hmap, FunctionalInequalities.Analysis.BakryEmery.cumulant_map_affine_408915f W _ (μR : Measure E) hexpR hk, hW]
        congr 1
        funext i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp only [Fin.cons_zero, hself]; rfl
        · simp only [Fin.cons_succ, hself]; rfl
      _ ≤ b * ‖u‖ ^ 2 := hb
  have hlim : Tendsto (fun R => ∑ J : Fin d → Fin m, FunctionalInequalities.Analysis.BakryEmery.cumulant (νR R) (d + 1)
      (Fin.cons (T R u) fun k => T R (EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2) atTop
      (𝓝 (∑ J : Fin d → Fin m, FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure E) (d + 1)
        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k)) ^ 2)) := by
    refine tendsto_finsetSum _ fun J _ => ?_
    refine (hcumd.eval ?_).pow 2
    rw [tendsto_pi_nhds]
    have hTv : ∀ v : E, Tendsto (fun R => T R v) atTop (𝓝 v) := fun v => by
      have := ((ContinuousLinearMap.apply ℝ E v).continuous.tendsto 1).comp hT
      simpa [Function.comp_def] using this
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa only [Fin.cons_zero] using hTv u
    · simpa only [Fin.cons_succ] using hTv (EuclideanSpace.basisFun (Fin m) ℝ (J k))
  exact le_of_tendsto hlim hbound
