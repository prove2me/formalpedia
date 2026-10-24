-- Prove2me | solution 1 for FunctionalInequalities.Analysis.symmetric_matrix_spectral_geometry_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:50:38.625161+00:00
-- url     : https://prove2.me/submissions/d1021c88-161d-4c2a-bf82-041e0a898199

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NoncommRing
import Theorems.Thm_FunctionalInequalities_Analysis_symmetric_matrix_sign_factorization_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_symmetric_matrix_sqrt_real_cfc_bridge_408915f

noncomputable section
open scoped MatrixOrder
noncomputable section
open scoped MatrixOrder
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
set_option maxHeartbeats 700000 in
theorem solution {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (hunit : IsUnit M) :
    let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M*M)
    let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
    let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
    B.PosSemidef ∧ S.PosSemidef ∧ Q.IsSymm ∧ B*B=M*M ∧ S*S=B ∧ S*Q*S=M ∧ Q*Q=1 ∧ IsUnit S ∧
    IsSelfAdjoint (Matrix.toEuclideanLin Q).toContinuousLinearMap ∧
    ∃ e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      e.toContinuousLinearMap = (Matrix.toEuclideanLin S).toContinuousLinearMap ∧
      IsSelfAdjoint e.toContinuousLinearMap := by
  let E := EuclideanSpace ℝ (Fin n)
  let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M*M)
  let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
  let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
  have hMM : 0 ≤ M*M := (FunctionalInequalities.Analysis.symmetric_matrix_sqrt_real_cfc_bridge_408915f M hM).1
  have hBn : 0 ≤ B := CFC.sqrt_nonneg _
  have hSn : 0 ≤ S := CFC.sqrt_nonneg _
  have hB : B.PosSemidef := by
    change (B-0).PosSemidef at hBn
    simpa only [sub_zero] using hBn
  have hS : S.PosSemidef := by
    change (S-0).PosSemidef at hSn
    simpa only [sub_zero] using hSn
  have hQh : Q.IsHermitian := IsSelfAdjoint.cfc (R := ℝ)
  have hQ : Q.IsSymm := Matrix.isHermitian_iff_isSymm.mp hQh
  have hBB : B*B=M*M := by
    simpa only [pow_two] using CFC.sq_sqrt (M*M) hMM
  obtain ⟨hSS,hSQS,hQQ⟩ := FunctionalInequalities.Analysis.symmetric_matrix_sign_factorization_408915f M hM
  have hQQ := hQQ hunit
  have hdetM : M.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp hunit)
  have hdetS : S.det ≠ 0 := by
    intro hz
    apply hdetM
    rw [← hSQS,Matrix.det_mul,Matrix.det_mul]
    change S.det * Q.det * S.det = 0
    rw [hz]
    ring
  have hSunit : IsUnit S := (Matrix.isUnit_iff_isUnit_det S).mpr (isUnit_iff_ne_zero.mpr hdetS)
  let f : E →ₗ[ℝ] E := Matrix.toEuclideanLin S
  have hfu : IsUnit f := by
    change IsUnit ((Matrix.toLinAlgEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) S)
    exact hSunit.map (Matrix.toLinAlgEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).toMonoidHom
  have hfi : Function.Injective f := LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot f).mp hfu)
  let e : E ≃L[ℝ] E := (LinearEquiv.ofInjectiveEndo f hfi).toContinuousLinearEquiv
  have he : e.toContinuousLinearMap = (Matrix.toEuclideanLin S).toContinuousLinearMap := by
    ext x
    rfl
  have hES : IsSelfAdjoint e.toContinuousLinearMap := by
    rw [he]
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hS.isHermitian)
  have hEQ : IsSelfAdjoint (Matrix.toEuclideanLin Q).toContinuousLinearMap :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hQh)
  exact ⟨hB,hS,hQ,hBB,hSS,hSQS,hQQ,hSunit,hEQ,e,he,hES⟩
