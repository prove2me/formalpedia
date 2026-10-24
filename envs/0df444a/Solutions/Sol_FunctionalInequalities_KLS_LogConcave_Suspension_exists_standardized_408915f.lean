-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.exists_standardized_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:21:40.754018+00:00
-- url     : https://prove2.me/submissions/b4a47715-2838-4800-afd8-7f9bc22496df

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
import Theorems.Thm_FunctionalInequalities_Analysis_inverseSqrt_mul_mul_inverseSqrt_408915f
import Theorems.Thm_FunctionalInequalities_Covariance_operator_map_continuousLinearEquiv_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_memLp_id_two_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_of_continuousLinearEquiv_map_408915f

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
universe u v
section Translation
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (ν : ProbabilityMeasure V) (c : V)
variable [CompleteSpace V]
/-- Translation does not change the covariance operator. -/
theorem FunctionalInequalities.Covariance.operator_translateLaw :
    Covariance.operator (Probability.translateLaw ν c : Measure V) = Covariance.operator (ν : Measure V) := by
  unfold Covariance.operator
  rw [Probability.coe_translateLaw, ProbabilityTheory.covarianceBilin_map_const_add]
end Translation
end
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
theorem FunctionalInequalities.Analysis.operatorMatrix_isUnit_iff (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    IsUnit (operatorMatrix b A) ↔ IsUnit A := by
  exact (LinearMap.isUnit_toMatrix_iff b.toBasis).trans
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.symm
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
theorem FunctionalInequalities.Analysis.inverseSqrtIn_isUnit (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) : IsUnit (inverseSqrtIn b A) := by
  have hp : (operatorMatrix b A).PosDef :=
    ((operatorMatrix_posSemidef_iff b A).mpr hpos).posDef_iff_isUnit.mpr
      ((operatorMatrix_isUnit_iff b A).mpr hunit)
  apply (operatorMatrix_isUnit_iff b _).mp
  rw [operatorMatrix_inverseSqrtIn]
  exact (IsStrictlyPositive.sqrt _ hp.inv.isStrictlyPositive).isUnit
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
omit [CompleteSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] [CompleteSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂] in
/-- The image of a log-concave law under a continuous linear equivalence is log-concave. -/
theorem FunctionalInequalities.KLS.LogConcave.mapContinuousLinearEquiv {ν : ProbabilityMeasure V₁} (hν : LogConcave ν) (T : V₁ ≃L[ℝ] V₂) :
    LogConcave (Probability.mapContinuousLinearEquiv ν T) :=
  hν.of_continuousLinearEquiv_map_408915f _ T.symm (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T).map_eq
end
end
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
omit [CompleteSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] in
omit [InnerProductSpace ℝ V₁] in
/-- Translation keeps a finite second moment. -/
theorem FunctionalInequalities.Probability.memLp_id_two_translateLaw
    (ν : ProbabilityMeasure V₁) (c : V₁) (h : MemLp id 2 (ν : Measure V₁)) :
    MemLp id 2 (translateLaw ν c : Measure V₁) := by
  rw [coe_translateLaw]
  exact (measurableEmbedding_addLeft c).memLp_map_measure_iff.mpr ((memLp_const c).add h)
end
end Euclidean
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
section MeasureHelpers
variable {E : Type*} [NormedAddCommGroup E]
section InnerProduct
variable [InnerProductSpace ℝ E]
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension in
/-- **Standardisation of a compactly supported log-concave law** with positive invertible covariance: the
law of `σ (x - a)`, with `σ = Cov^{-1/2}` and `a` the mean, is isotropic, log-concave and compactly
supported. -/
theorem solution [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ProbabilityMeasure E) (hLC : FunctionalInequalities.KLS.LogConcave μ)
    (hc : IsCompact (μ : Measure E).support)
    (hpos : (FunctionalInequalities.Covariance.operator (μ : Measure E)).IsPositive)
    (hunit : IsUnit (FunctionalInequalities.Covariance.operator (μ : Measure E))) :
    ∃ (η : ProbabilityMeasure E) (W : E ≃L[ℝ] E),
      (W : E →L[ℝ] E) = FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator (μ : Measure E)) ∧
      FunctionalInequalities.KLS.Isotropic η ∧ FunctionalInequalities.KLS.LogConcave η ∧ IsCompact (η : Measure E).support ∧
      (η : Measure E) = (μ : Measure E).map (fun x => W (x - ∫ y, y ∂(μ : Measure E))) := by
  let A : E →L[ℝ] E := FunctionalInequalities.Covariance.operator (μ : Measure E)
  let σ : E →L[ℝ] E := FunctionalInequalities.Analysis.inverseSqrt A
  have hσ : IsUnit σ := by
    change IsUnit (FunctionalInequalities.Analysis.inverseSqrtIn (stdOrthonormalBasis ℝ E) A)
    exact FunctionalInequalities.Analysis.inverseSqrtIn_isUnit (stdOrthonormalBasis ℝ E) A hpos hunit
  let W : E ≃L[ℝ] E := ContinuousLinearEquiv.ofUnit hσ.unit
  have hW : (W : E →L[ℝ] E) = σ := by
    change (↑hσ.unit : E →L[ℝ] E) = σ
    exact hσ.unit_spec
  have hWx : ∀ x, W x = σ x := fun x => by rw [← hW]; rfl
  let a : E := ∫ y, y ∂(μ : Measure E)
  let ν' : ProbabilityMeasure E := FunctionalInequalities.Probability.translateLaw μ (-a)
  let η : ProbabilityMeasure E := FunctionalInequalities.Probability.mapContinuousLinearEquiv ν' W
  have hηcoe : (η : Measure E) = (ν' : Measure E).map W := rfl
  have hmeas : Measurable fun x : E => W (x - a) :=
    (W.continuous.comp (continuous_id.sub continuous_const)).measurable
  have hmap : (η : Measure E) = (μ : Measure E).map (fun x => W (x - a)) := by
    rw [hηcoe, FunctionalInequalities.Probability.coe_translateLaw,
      Measure.map_map W.continuous.measurable (measurable_const_add (-a))]
    congr 1
    funext x
    simp [neg_add_eq_sub]
  have hμlp : MemLp id 2 (μ : Measure E) := hLC.memLp_id_two_408915f
  have hint : Integrable id (μ : Measure E) := hμlp.integrable (by norm_num)
  have ht : MemLp id 2 (ν' : Measure E) := FunctionalInequalities.Probability.memLp_id_two_translateLaw μ (-a) hμlp
  have hηlp : MemLp id 2 (η : Measure E) := by
    rw [hηcoe, memLp_map_measure_iff measurable_id.aestronglyMeasurable W.continuous.aemeasurable]
    simpa [Function.comp_def] using (W : E →L[ℝ] E).comp_memLp' ht
  have hzero : ∫ x, x ∂(ν' : Measure E) = 0 :=
    FunctionalInequalities.Probability.integral_id_translateLaw_neg_integral μ hint
  have hmean : ∫ x, x ∂(η : Measure E) = 0 := by
    rw [hηcoe]
    change ∫ x, id x ∂((ν' : Measure E).map W) = 0
    rw [integral_map W.continuous.aemeasurable hηlp.aestronglyMeasurable]
    simp only [id_eq]
    rw [W.integral_comp_comm]
    simpa using congrArg W hzero
  have hself : (σ.adjoint : E →L[ℝ] E) = σ := (FunctionalInequalities.Analysis.inverseSqrt_spec A hpos hunit).2.1.adjoint_eq
  have halg : (σ.comp A).comp σ = 1 := by
    ext x
    simpa [σ, ContinuousLinearMap.comp_apply] using
      congrArg (fun T : E →L[ℝ] E => T x) (FunctionalInequalities.Analysis.inverseSqrt_mul_mul_inverseSqrt_408915f A hpos hunit)
  have hiso : FunctionalInequalities.KLS.Isotropic η := by
    refine ⟨hηlp, hmean, ?_⟩
    rw [hηcoe, FunctionalInequalities.Covariance.operator_map_continuousLinearEquiv_408915f, FunctionalInequalities.Covariance.operator_translateLaw, hW,
      hself]
    exact halg
  have hLCη : FunctionalInequalities.KLS.LogConcave η := (hLC.translateLaw (-a)).mapContinuousLinearEquiv W
  have hcη : IsCompact (η : Measure E).support := by
    have hK : IsCompact ((fun x : E => W (x - a)) '' (μ : Measure E).support) :=
      hc.image (W.continuous.comp (continuous_id.sub continuous_const))
    refine hK.of_isClosed_subset Measure.isClosed_support
      (Measure.support_subset_of_isClosed hK.isClosed ?_)
    have hinj : Function.Injective fun x : E => W (x - a) := fun x y hxy =>
      sub_left_injective (W.injective hxy)
    rw [mem_ae_iff, hmap, Measure.map_apply hmeas hK.isClosed.measurableSet.compl,
      Set.preimage_compl, Set.preimage_image_eq _ hinj]
    exact Measure.measure_compl_support
  exact ⟨η, W, hW, hiso, hLCη, hcη, hmap⟩
