-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.cumulantEnergy_eq_energyForm_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:28:24.050669+00:00
-- url     : https://prove2.me/submissions/3b1a7ad7-4a09-46d5-beb1-e14a159d09b4

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Conjugation

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

section
noncomputable section
open scoped MatrixOrder RealInnerProductSpace
section
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

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
open FunctionalInequalities.Analysis.CoordinateTensor
variable {n : ℕ}
private lemma FunctionalInequalities.KLS.BKL.energy_inverse_conjugate
    {M : Type*} [MonoidWithZero M] (A P : M)
    (hA : IsUnit A) (hP : IsUnit P) :
    Ring.inverse (P * A * P) =
      Ring.inverse P * Ring.inverse A * Ring.inverse P := by
  rcases hA with ⟨a, rfl⟩
  rcases hP with ⟨p, rfl⟩
  change Ring.inverse (↑(p * a * p) : M) =
    Ring.inverse (↑p : M) * Ring.inverse (↑a : M) * Ring.inverse (↑p : M)
  rw [Ring.inverse_unit (p * a * p), Ring.inverse_unit p, Ring.inverse_unit a]
  simp only [mul_inv_rev, Units.val_mul, mul_assoc]
private lemma FunctionalInequalities.KLS.BKL.energy_coordinate_gram
    (R S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hR : IsSelfAdjoint R) (hS : IsSelfAdjoint S)
    (x y : EuclideanSpace ℝ (Fin n)) :
    (∑ j : Fin n,
      ⟪x, R (S (EuclideanSpace.basisFun (Fin n) ℝ j))⟫ *
        ⟪y, R (S (EuclideanSpace.basisFun (Fin n) ℝ j))⟫) =
      ⟪x, (R * S * S * R) y⟫ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hm (v w : EuclideanSpace ℝ (Fin n)) :
      ⟪v, R (S w)⟫ = ⟪S (R v), w⟫ := by
    rw [← R.adjoint_inner_left (S w) v, hR.adjoint_eq,
      ← S.adjoint_inner_left w (R v), hS.adjoint_eq]
  change (∑ j, ⟪x, R (S (b j))⟫ * ⟪y, R (S (b j))⟫) = _
  simp only [hm]
  have hf (j : Fin n) : ⟪S (R y), b j⟫ = ⟪b j, S (R y)⟫ :=
    real_inner_comm _ _
  simp only [hf]
  rw [b.sum_inner_mul_inner]
  rw [← S.adjoint_inner_right (R x) (S (R y)), hS.adjoint_eq,
    ← R.adjoint_inner_right x (S (S (R y))), hR.adjoint_eq]
  rfl
private lemma FunctionalInequalities.KLS.BKL.energy_tensor_square (r : ℕ)
    (c : Fin n → Fin n → ℝ) (T : (Fin r → Fin n) → ℝ) :
    (∑ J : Fin r → Fin n,
      (∑ K : Fin r → Fin n, (∏ s, c (J s) (K s)) * T K) ^ 2) =
      ∑ K : Fin r → Fin n, ∑ L : Fin r → Fin n,
        T K * T L * ∏ s, (∑ j : Fin n, c j (K s) * c j (L s)) := by
  classical
  calc
    (∑ J : Fin r → Fin n,
        (∑ K : Fin r → Fin n, (∏ s, c (J s) (K s)) * T K) ^ 2) =
        ∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n,
          ∑ L : Fin r → Fin n,
            T K * T L * ∏ s, (c (J s) (K s) * c (J s) (L s)) := by
      simp only [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro J _
      apply Finset.sum_congr rfl
      intro K _
      apply Finset.sum_congr rfl
      intro L _
      rw [Finset.prod_mul_distrib]
      ring
    _ = ∑ K : Fin r → Fin n, ∑ L : Fin r → Fin n,
          ∑ J : Fin r → Fin n,
            T K * T L * ∏ s, (c (J s) (K s) * c (J s) (L s)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro K _
      rw [Finset.sum_comm]
    _ = ∑ K : Fin r → Fin n, ∑ L : Fin r → Fin n,
          T K * T L * ∏ s, (∑ j : Fin n, c j (K s) * c j (L s)) := by
      apply Finset.sum_congr rfl
      intro K _
      apply Finset.sum_congr rfl
      intro L _
      rw [Fintype.prod_sum
        (fun (s : Fin r) (j : Fin n) => c j (K s) * c j (L s)),
        Finset.mul_sum]
/-- **The cumulant energy as the energy form in conjugated coordinates** (BKL (83) and (85)): for a law `ν` with
positive invertible covariance `A` and any self-adjoint invertible `P`,
`E_{r+1}(u) = |κ_{r+1}(u)|²_A = F(P A P, P^{⊗r} κ_{r+1}(u))`, where `(P^{⊗r} κ_{r+1}(u))_K = κ_{r+1}(u, P e_{K_1}, …, P e_{K_r})`. -/
theorem solution (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hpos : (FunctionalInequalities.Covariance.operator ν).IsPositive) (hunit : IsUnit (FunctionalInequalities.Covariance.operator ν))
    (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hP : IsSelfAdjoint P) (hPu : IsUnit P)
    (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    FunctionalInequalities.KLS.BKL.cumulantEnergy ν r u =
      FunctionalInequalities.Analysis.CoordinateTensor.energyForm (P * FunctionalInequalities.Covariance.operator ν * P)
        (fun K : Fin r → Fin n => FunctionalInequalities.Analysis.BakryEmery.cumulant ν (r + 1) (Fin.cons u fun s => P (EuclideanSpace.basisFun (Fin n) ℝ (K s)))) := by
  classical
  let A := FunctionalInequalities.Covariance.operator ν
  let S := FunctionalInequalities.Analysis.inverseSqrt A
  let R := Ring.inverse P
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let f := (FunctionalInequalities.Analysis.BakryEmery.cumulant ν (r + 1)).curryLeft u
  let c := fun j k : Fin n => ⟪b k, R (S (b j))⟫
  let T := fun K : Fin r → Fin n => f (fun s => P (b (K s)))
  have hspec := FunctionalInequalities.Analysis.inverseSqrt_spec A hpos hunit
  have hi : Ring.inverse (P * A * P) = R * Ring.inverse A * R :=
    FunctionalInequalities.KLS.BKL.energy_inverse_conjugate A P hunit hPu
  have hoperator : R * S * S * R = Ring.inverse (P * A * P) := by
    rw [mul_assoc R S S, hspec.2.2.1]
    exact hi.symm
  have he (x : EuclideanSpace ℝ (Fin n)) :
      (∑ k, ⟪b k, R x⟫ • P (b k)) = x := by
    simpa only [map_sum, map_smul, ← mul_apply_eq_comp,
      Ring.mul_inverse_cancel P hPu, one_apply_eq_self] using
      congrArg P (b.sum_repr' (Ring.inverse P x))
  have hex (J : Fin r → Fin n) :
      f (fun s => S (b (J s))) =
        ∑ K : Fin r → Fin n, (∏ s, c (J s) (K s)) * T K := by
    have hv :
        (fun s : Fin r => S (b (J s))) =
          (fun s => ∑ k, c (J s) k • P (b k)) := by
      funext s
      exact (he _).symm
    rw [hv]
    simp only [ContinuousMultilinearMap.map_sum,
      ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
    rfl
  have hc (k l : Fin n) :
      (∑ j : Fin n, c j k * c j l) =
        ⟪b k, Ring.inverse (P * A * P) (b l)⟫ := by
    change (∑ j : Fin n, ⟪b k, R (S (b j))⟫ * ⟪b l, R (S (b j))⟫) = _
    rw [FunctionalInequalities.KLS.BKL.energy_coordinate_gram R S hP.ringInverse hspec.2.1, hoperator]
  calc
    FunctionalInequalities.KLS.BKL.cumulantEnergy ν r u =
        ∑ J : Fin r → Fin n,
          (∑ K : Fin r → Fin n, (∏ s, c (J s) (K s)) * T K) ^ 2 := by
      unfold FunctionalInequalities.KLS.BKL.cumulantEnergy
      apply Finset.sum_congr rfl
      intro J _
      exact congrArg (fun t : ℝ => t ^ 2) (hex J)
    _ = ∑ K : Fin r → Fin n, ∑ L : Fin r → Fin n,
          T K * T L * ∏ s, (∑ j : Fin n, c j (K s) * c j (L s)) :=
      FunctionalInequalities.KLS.BKL.energy_tensor_square r c T
    _ = FunctionalInequalities.Analysis.CoordinateTensor.energyForm (P * FunctionalInequalities.Covariance.operator ν * P)
          (fun K : Fin r → Fin n =>
            FunctionalInequalities.Analysis.BakryEmery.cumulant ν (r + 1)
              (Fin.cons u fun s => P (EuclideanSpace.basisFun (Fin n) ℝ (K s)))) := by
      simp only [hc]
      rfl
