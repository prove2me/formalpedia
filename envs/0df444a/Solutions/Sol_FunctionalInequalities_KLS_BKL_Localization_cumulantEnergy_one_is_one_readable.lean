-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.cumulantEnergy_one_is_one_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:28:05.670484+00:00
-- url     : https://prove2.me/submissions/96b8e67e-f5ff-4723-bb2a-b0790d210248

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Base
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_two_eq_centered_moment_of_integrable_exp_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_memLp_of_polynomial_bound_of_integrable_exp_readable

section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- At the initial parameters the posterior is the prior. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_zero (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) : compactPosterior μ hc 0 0 = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change (μ : Measure E).tilted (quadraticExponent (0 : E) 0) = _
  have he : quadraticExponent (0 : E) (0 : E →L[ℝ] E) = 0 := by funext x; simp [quadraticExponent]
  rw [he, tilted_zero]
end
end
end

section
noncomputable section
open scoped RealInnerProductSpace MatrixOrder
section
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
/-- The matrix inverse of a unit's matrix is the matrix of `Ring.inverse`. -/
theorem FunctionalInequalities.Analysis.operatorMatrix_ringInverse (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) (hA : IsUnit A) :
    (operatorMatrix b A)⁻¹ = operatorMatrix b (Ring.inverse A) := by
  apply Matrix.inv_eq_right_inv
  rw [← operatorMatrix_mul, Ring.mul_inverse_cancel A hA, operatorMatrix_one]
end OperatorMatrix
end
end
end

section
noncomputable section
open scoped MatrixOrder RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_inverseSqrtIn (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    operatorMatrix b (inverseSqrtIn b A) = CFC.sqrt ((operatorMatrix b A)⁻¹) :=
  operatorMatrix_operatorOfMatrix b _
/-- Uniqueness of the positive branch: any positive `S` with `S² = A⁻¹` equals `inverseSqrtIn b A`. -/
theorem FunctionalInequalities.Analysis.inverseSqrtIn_unique (b : OrthonormalBasis ι ℝ E) (A S : E →L[ℝ] E)
    (hunit : IsUnit A) (hS : S.IsPositive) (hSquare : S * S = Ring.inverse A) :
    inverseSqrtIn b A = S := by
  apply operatorMatrix_injective b
  rw [operatorMatrix_inverseSqrtIn]
  apply CFC.sqrt_unique
  · rw [← operatorMatrix_mul, hSquare, operatorMatrix_ringInverse b A hunit]
  · exact ((operatorMatrix_posSemidef_iff b S).mpr hS).nonneg
theorem FunctionalInequalities.Analysis.inverseSqrt_unique (A S : E →L[ℝ] E)
    (hunit : IsUnit A) (hS : S.IsPositive) (hSquare : S * S = Ring.inverse A) :
    inverseSqrt A = S := inverseSqrtIn_unique _ A S hunit hS hSquare
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
open Set
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- At the initial pair `c = Q = 0` the diffusion coefficient is `Id`. -/
theorem FunctionalInequalities.KLS.Isotropic.inverseSqrt_covariance_compactPosterior_zero
    (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    inverseSqrt (Covariance.operator (compactPosterior μ hc 0 0 : Measure E)) =
      ContinuousLinearMap.id ℝ E := by
  rw [compactPosterior_zero, hiso.covariance_identity]
  change inverseSqrt (1 : E →L[ℝ] E) = 1
  apply inverseSqrt_unique _ _ isUnit_one
  · exact ContinuousLinearMap.isPositive_one
  · simp
variable {ι : Type*} [Fintype ι]
end
end
end

section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section SecondCumulant
/-- One exponential moment gives `id ∈ L²(μ)`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.memLp_id_two_of_integrable_exp (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    MemLp id 2 μ := by
  have hn : MemLp (fun x : E => ‖x‖) 2 μ := by
    apply memLp_of_polynomial_bound_of_integrable_exp_readable μ hr hexp continuous_norm (C := 1) (k := 1)
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
  exact cumulant_two_eq_centered_moment_of_integrable_exp_readable μ hr hexp u v
end SecondCumulant
end
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
 theorem solution
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hiso : FunctionalInequalities.KLS.Isotropic μ) (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    FunctionalInequalities.KLS.BKL.cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) 1 u = 1 := by
  classical
  have hexp :
      Integrable
        (fun x : EuclideanSpace ℝ (Fin n) => Real.exp ((1 : ℝ) * ‖x‖))
        (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
    FunctionalInequalities.Probability.Posterior.integrable_exp_of_compact μ hc (by fun_prop)
  have hsqrt :
      FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))) =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [FunctionalInequalities.Probability.Posterior.compactPosterior_zero] using
      FunctionalInequalities.KLS.Isotropic.inverseSqrt_covariance_compactPosterior_zero μ hc hiso
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let e : Fin n ≃ (Fin 1 → Fin n) :=
    { toFun := fun j _ => j
      invFun := fun J => J 0
      left_inv := fun _ => rfl
      right_inv := by
        intro J
        funext i
        fin_cases i
        rfl }
  have hcum (j : Fin n) :
      FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
          (Fin.cons u (fun _ : Fin 1 => b j)) = ⟪u, b j⟫ := by
    have h :=
      FunctionalInequalities.Analysis.BakryEmery.cumulant_two_eq_covariance_of_integrable_exp
        (μ : Measure (EuclideanSpace ℝ (Fin n))) (by norm_num) hexp u (b j)
    calc
      FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
          (Fin.cons u (fun _ : Fin 1 => b j)) =
          FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2 ![u, b j] := by
            congr 1
            funext i
            fin_cases i <;> rfl
      _ = ⟪FunctionalInequalities.Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n))) u, b j⟫ := h
      _ = ⟪u, b j⟫ := by
        rw [hiso.covariance_identity]
        rfl
  rw [FunctionalInequalities.KLS.BKL.cumulantEnergy, hsqrt]
  change
    ∑ J : Fin 1 → Fin n,
        FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
          (Fin.cons u (fun k => b (J k))) ^ 2 = 1
  calc
    ∑ J : Fin 1 → Fin n,
        FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
          (Fin.cons u (fun k => b (J k))) ^ 2 =
        ∑ j : Fin n,
          FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
            (Fin.cons u (fun k => b ((e j) k))) ^ 2 :=
      (e.sum_comp
        (fun J : Fin 1 → Fin n =>
          FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
            (Fin.cons u (fun k => b (J k))) ^ 2)).symm
    _ = ∑ j : Fin n,
          FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
            (Fin.cons u (fun _ : Fin 1 => b j)) ^ 2 := rfl
    _ = ∑ j : Fin n, ⟪u, b j⟫ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hcum]
    _ = ∑ j : Fin n, ⟪u, b j⟫ * ⟪b j, u⟫ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [real_inner_comm (b j) u]
      ring
    _ = ⟪u, u⟫ := b.sum_inner_mul_inner u u
    _ = 1 := by
      rw [real_inner_self_eq_norm_mul_norm, hu]
      norm_num
