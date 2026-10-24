-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.sum_sq_pairTerm_ofFn_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:17:31.346627+00:00
-- url     : https://prove2.me/submissions/ce5255be-5004-4b97-8601-f8a9dd9f36d7

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_FunctionalInequalities_Analysis_inverseSqrt_mul_mul_inverseSqrt_408915f

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
noncomputable section
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem FunctionalInequalities.Analysis.directional_contDiff {f : E → F} (hf : ContDiff ℝ ∞ f) (hs : List E) :
    ContDiff ℝ ∞ (directional hs f) := by
  induction hs with
  | nil => exact hf
  | cons h hs IH =>
    exact (ContinuousLinearMap.apply ℝ F h).contDiff.comp (IH.fderiv_right (by simp))
private theorem FunctionalInequalities.Analysis.directional_two {f : E → F} (hf : ContDiff ℝ ∞ f) (v w x : E) :
    directional [v, w] f x = fderiv ℝ (fderiv ℝ f) x v w := by
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v = _
  have hDf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [fderiv_clm_apply (hDf.differentiable (by simp) x) (differentiableAt_const w)]
  simp
/-- Adjacent directional derivatives commute by genuine real C² symmetry. -/
theorem FunctionalInequalities.Analysis.directional_swap {f : E → F} (hf : ContDiff ℝ ∞ f) (hs : List E) (v w : E) :
    directional (v :: w :: hs) f = directional (w :: v :: hs) f := by
  funext x
  have hg := directional_contDiff hf hs
  have he (u t : E) : directional (u :: t :: hs) f x = directional [u,t] (directional hs f) x := rfl
  rw [he, he, directional_two hg, directional_two hg]
  exact hg.contDiffAt.isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top) v w
/-- Full permutation symmetry follows from adjacent swaps; no tensor symmetry is a premise. -/
theorem FunctionalInequalities.Analysis.directional_perm {f : E → F} (hf : ContDiff ℝ ∞ f) {hs ks : List E}
    (h : hs.Perm ks) : directional hs f = directional ks f := by
  induction h with
  | nil => rfl
  | cons v h IH =>
    change (fun x => fderiv ℝ (directional _ f) x v) = (fun x => fderiv ℝ (directional _ f) x v)
    rw [IH]
  | swap v w hs => exact directional_swap hf hs w v
  | trans h1 h2 IH1 IH2 => exact IH1.trans IH2
/-- The directional list convention is exactly the raw iterated Fréchet derivative. -/
theorem FunctionalInequalities.Analysis.directional_ofFn {f : E → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) (h : Fin m → E) (x : E) :
    directional (List.ofFn h) f x = iteratedFDeriv ℝ m f x h := by
  induction m generalizing x with
  | zero => simp [directional]
  | succ m IH =>
    rw [List.ofFn_succ]
    change fderiv ℝ (directional (List.ofFn (Fin.tail h)) f) x (h 0) = _
    have he : directional (List.ofFn (Fin.tail h)) f =
        fun y => iteratedFDeriv ℝ m f y (Fin.tail h) := funext (fun y => IH (Fin.tail h) y)
    rw [he]
    exact ((hf.differentiable_iteratedFDeriv (m := m)
      (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m)) x).iteratedFDeriv_succ_apply_left').symm
/-- Raw real C∞ iterated derivatives are symmetric under every slot permutation. -/
theorem FunctionalInequalities.Analysis.iteratedFDeriv_perm {f : E → F} (hf : ContDiff ℝ ∞ f) (m : ℕ)
    (h : Fin m → E) (σ : Equiv.Perm (Fin m)) (x : E) :
    iteratedFDeriv ℝ m f x (h ∘ σ) = iteratedFDeriv ℝ m f x h := by
  rw [← directional_ofFn hf, ← directional_ofFn hf]
  exact congrFun (directional_perm hf (σ.ofFn_comp_perm h)) x
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
section CompactSupport
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
/-- A law with compact support has every exponential moment. -/
theorem FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp (μ : Measure F) [IsFiniteMeasure μ]
    (hc : IsCompact μ.support) (r : ℝ) : Integrable (fun x => Real.exp (r * ‖x‖)) μ := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : F)
  refine (integrable_const (Real.exp (|r| * max R 0))).mono' (by fun_prop) ?_
  filter_upwards [μ.support_mem_ae] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    r * ‖x‖ ≤ |r| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |r| * max R 0 := by
      gcongr
      exact (by simpa using hR hx : ‖x‖ ≤ R).trans (le_max_left _ _)
end CompactSupport
section GradientJets
omit [BorelSpace E] in
/-- Literal scalar-cumulant meaning of `cumulantVector`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.cumulantVector_inner (μ : Measure E) (hs : List E) (w : E) :
    ⟪cumulantVector μ hs, w⟫ =
      cumulant μ (hs.length + 1) (Fin.snoc (fun i => hs.get i) w) := by
  rw [cumulantVector, InnerProductSpace.toDual_symm_apply,
    ContinuousMultilinearMap.curryRight_apply]
end GradientJets
section CumulantSymmetry
/-- The cumulant tensors of a compactly supported law are symmetric: `κ_m(h ∘ σ) = κ_m(h)` for every permutation `σ`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.cumulant_comp_perm_of_compact (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    {m : ℕ} (σ : Equiv.Perm (Fin m)) (h : Fin m → E) :
    cumulant (μ : Measure E) m (h ∘ σ) = cumulant (μ : Measure E) m h := by
    have hΛ : ContDiff ℝ ∞ (logLaplace (μ : Measure E)) :=
      contDiff_logLaplace _ (compact_support_integrable_exp _ hc)
    simp only [cumulant]
    exact iteratedFDeriv_perm hΛ m h σ 0
end CumulantSymmetry
end
end
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
section S4Section6Pointwise
open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
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
namespace FunctionalInequalities.KLS.BKL
end FunctionalInequalities.KLS.BKL
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.BKL
variable {n : ℕ}
section Masks
theorem FunctionalInequalities.KLS.BKL.sum_snoc_split {ι : Type*} [Fintype ι] {k : ℕ} (F : (Fin (k+1) → ι) → ℝ) :
    ∑ J : Fin (k+1) → ι, F J = ∑ j : ι, ∑ J' : Fin k → ι, F (Fin.snoc J' j) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (k+1) => ι)).sum_comp, Fintype.sum_prod_type]
  rfl
end Masks
section Algebra
theorem FunctionalInequalities.KLS.BKL.covariance_isPositive (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator ν v, v⟫) :
    (Covariance.operator ν).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff' _).mpr
  refine ⟨Covariance.operator_isSelfAdjoint _, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · exact (hApos v hv).le
theorem FunctionalInequalities.KLS.BKL.inverseSqrt_inner_left (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hA : IsUnit (Covariance.operator ν))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator ν v, v⟫) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪inverseSqrt (Covariance.operator ν) x, y⟫ = ⟪x, inverseSqrt (Covariance.operator ν) y⟫ := by
  have hsa := (inverseSqrt_spec _ (covariance_isPositive ν hApos) hA).2.1
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) x y
theorem FunctionalInequalities.KLS.BKL.inner_sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hA : IsUnit (Covariance.operator ν))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator ν v, v⟫) (z : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    ⟪z, sigmaBasis ν j⟫ = inverseSqrt (Covariance.operator ν) z j := by
  unfold sigmaBasis
  rw [← inverseSqrt_inner_left ν hA hApos, EuclideanSpace.inner_basisFun_real]
theorem FunctionalInequalities.KLS.BKL.sum_inner_sigmaBasis_mul (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hA : IsUnit (Covariance.operator ν))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator ν v, v⟫) (z y : EuclideanSpace ℝ (Fin n)) :
    ∑ j, ⟪z, sigmaBasis ν j⟫ * ⟪y, sigmaBasis ν j⟫ = ⟪z, Ring.inverse (Covariance.operator ν) y⟫ := by
  have hsq := (inverseSqrt_spec _ (covariance_isPositive ν hApos) hA).2.2.1
  have h := (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner
    (inverseSqrt (Covariance.operator ν) z) (inverseSqrt (Covariance.operator ν) y)
  simp only [EuclideanSpace.inner_basisFun_real, EuclideanSpace.basisFun_inner] at h
  simp only [inner_sigmaBasis ν hA hApos]
  rw [h, inverseSqrt_inner_left ν hA hApos, ← mul_apply_eq_comp, hsq]
theorem FunctionalInequalities.KLS.BKL.sum_mul_inner_sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hA : IsUnit (Covariance.operator ν))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator ν v, v⟫) (y : EuclideanSpace ℝ (Fin n))
    (v : Fin n → ℝ) :
    ∑ j, v j * ⟪y, sigmaBasis ν j⟫ = ⟪y, inverseSqrt (Covariance.operator ν) (WithLp.toLp 2 v)⟫ := by
  rw [← inverseSqrt_inner_left ν hA hApos]
  simp only [inner_sigmaBasis ν hA hApos, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp
theorem FunctionalInequalities.KLS.BKL.inner_cov_inverseSqrt_eq_sum (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hA : IsUnit (Covariance.operator ν))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator ν v, v⟫) (v : Fin n → ℝ) :
    ⟪Covariance.operator ν (inverseSqrt (Covariance.operator ν) (WithLp.toLp 2 v)),
      inverseSqrt (Covariance.operator ν) (WithLp.toLp 2 v)⟫ = ∑ j, v j ^ 2 := by
  rw [← inverseSqrt_inner_left ν hA hApos, ← mul_apply_eq_comp,
    ← mul_apply_eq_comp,
    inverseSqrt_mul_mul_inverseSqrt_408915f _ (covariance_isPositive ν hApos) hA]
  simp only [one_apply_eq_self, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [sq]
theorem FunctionalInequalities.KLS.BKL.inner_cumulantVector_ofFn (μ : Measure (EuclideanSpace ℝ (Fin n))) {c : ℕ}
    (g : Fin c → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪cumulantVector μ (List.ofFn g), x⟫ = cumulant μ (c + 1) (Fin.snoc g x) := by
  rw [cumulantVector_inner]
  have haux : ∀ (N : ℕ) (hN : N = c) (g' : Fin N → EuclideanSpace ℝ (Fin n)),
      (∀ i, g' i = g (Fin.cast hN i)) →
        cumulant μ (N + 1) (Fin.snoc g' x) = cumulant μ (c + 1) (Fin.snoc g x) := by
    intro N hN g' hg'
    subst hN
    have : g' = g := by
      funext i
      simpa using hg' i
    rw [this]
  exact haux _ (List.length_ofFn (f := g)) _ (fun i => List.get_ofFn g i)
theorem FunctionalInequalities.KLS.BKL.cumulant_snoc_eq_cons (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support) {c : ℕ}
    (g : Fin c → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (c + 1) (Fin.snoc g x) =
      cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (c + 1) (Fin.cons x g) := by
  have h : (Fin.snoc g x : Fin (c + 1) → EuclideanSpace ℝ (Fin n)) =
      (Fin.cons x g : Fin (c + 1) → EuclideanSpace ℝ (Fin n)) ∘ finRotate (c + 1) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.coeSucc_eq_succ]
  rw [h, cumulant_comp_perm_of_compact ν hc]
/-- Row contraction (BKL (101)–(102) at the level of finite arrays; `Analysis/Tensor/Coordinate.lean`): a row
bound `Σ_j (Σ_k v_k T(j,k))² ≤ β Σ_k v_k²` for every `v` gives `Σ_i Σ_j (Σ_k S(i,k) T(j,k))² ≤ β Σ_i Σ_k S(i,k)²`. -/
theorem FunctionalInequalities.KLS.BKL.sum_sq_contract_le_rows {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (T : ρ → κ → ℝ) {β : ℝ}
    (hT : ∀ v : κ → ℝ, ∑ j, (∑ k, v k * T j k) ^ 2 ≤ β * ∑ k, v k ^ 2) (S : ι → κ → ℝ) :
    ∑ i, ∑ j, (∑ k, S i k * T j k) ^ 2 ≤ β * ∑ i, ∑ k, S i k ^ 2 := by
  calc
    ∑ i, ∑ j, (∑ k, S i k * T j k) ^ 2 ≤ ∑ i, (β * ∑ k, S i k ^ 2) :=
      Finset.sum_le_sum (fun i _ => hT (S i))
    _ = β * ∑ i, ∑ k, S i k ^ 2 := by rw [Finset.mul_sum]
namespace FunctionalInequalities.KLS.BKL
end FunctionalInequalities.KLS.BKL
open FunctionalInequalities.KLS.BKL in
/-- **Row contraction for one mask** (BKL (101)–(102)): with `c` selected and `c₂` complementary slots,
`Σ_{J₁, J₂} ⟪κ_{c+2}(u, w_{J₁}, ·), A⁻¹ κ_{c₂+1}(w_{J₂}, ·)⟫² ≤ β E_{c+2}(u)` whenever
`E_{c₂+1}(v) ≤ β ⟪A v, v⟫` for every `v` (hypothesis (100) at order `c₂ + 1`). -/
theorem solution (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hA : IsUnit (FunctionalInequalities.Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n)))))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪FunctionalInequalities.Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    {c c₂ : ℕ} (β : ℝ)
    (h100 : ∀ v : EuclideanSpace ℝ (Fin n),
      FunctionalInequalities.KLS.BKL.cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) c₂ v ≤
        β * ⟪FunctionalInequalities.Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    (u : EuclideanSpace ℝ (Fin n)) :
    ∑ J₁ : Fin c → Fin n, ∑ J₂ : Fin c₂ → Fin n,
      FunctionalInequalities.KLS.BKL.pairTerm (ν : Measure (EuclideanSpace ℝ (Fin n))) u
        (List.ofFn fun i => FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₁ i))
        (List.ofFn fun i => FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₂ i)) ≤
      β * FunctionalInequalities.KLS.BKL.cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (c + 1) u := by
  simp only [FunctionalInequalities.KLS.BKL.pairTerm, ← List.ofFn_cons, ← FunctionalInequalities.KLS.BKL.sum_inner_sigmaBasis_mul _ hA hApos]
  refine le_trans (FunctionalInequalities.KLS.BKL.sum_sq_contract_le_rows (β := β)
    (fun (J₂ : Fin c₂ → Fin n) (j : Fin n) =>
      ⟪FunctionalInequalities.Analysis.BakryEmery.cumulantVector (ν : Measure (EuclideanSpace ℝ (Fin n)))
        (List.ofFn fun i => FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₂ i)),
        FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) j⟫) ?_
    (fun (J₁ : Fin c → Fin n) (j : Fin n) =>
      ⟪FunctionalInequalities.Analysis.BakryEmery.cumulantVector (ν : Measure (EuclideanSpace ℝ (Fin n)))
        (List.ofFn (Fin.cons u fun i => FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₁ i))),
        FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) j⟫)) (le_of_eq ?_)
  · intro v
    have h1 : ∀ J₂ : Fin c₂ → Fin n,
        ∑ j, v j * ⟪FunctionalInequalities.Analysis.BakryEmery.cumulantVector (ν : Measure (EuclideanSpace ℝ (Fin n)))
          (List.ofFn fun i => FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₂ i)),
          FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) j⟫ =
        FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (c₂ + 1)
          (Fin.cons (FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
            (WithLp.toLp 2 v)) fun i => FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₂ i)) := by
      intro J₂
      rw [FunctionalInequalities.KLS.BKL.sum_mul_inner_sigmaBasis _ hA hApos, FunctionalInequalities.KLS.BKL.inner_cumulantVector_ofFn, FunctionalInequalities.KLS.BKL.cumulant_snoc_eq_cons ν hc]
    simp only [h1]
    have h2 := h100 (FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
      (WithLp.toLp 2 v))
    rw [FunctionalInequalities.KLS.BKL.inner_cov_inverseSqrt_eq_sum _ hA hApos] at h2
    exact h2
  · congr 1
    unfold FunctionalInequalities.KLS.BKL.cumulantEnergy
    rw [FunctionalInequalities.KLS.BKL.sum_snoc_split, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun J₁ _ => ?_
    rw [FunctionalInequalities.KLS.BKL.inner_cumulantVector_ofFn, ← Fin.cons_snoc_eq_snoc_cons]
    congr 3
    exact (Fin.comp_snoc (FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n)))) J₁ j).symm
