-- Prove2me | solution 1 for Bl.general_b_fact_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:05.028695+00:00
-- url     : https://prove2.me/submissions/a65fc965-40fc-4e49-a588-d07db17a139b

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactForm_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_form
namespace Bl.general_b_fact_form
theorem _root_.solution :
  ∀ {n : Nat} {N N' U U' : Matrix.{0, 0, 0} (Fin n) (Fin n) Complex},
  Matrix.BlockTriangular.{0, 0, 0} N (DFunLike.coe.{1, 1, 1} OrderDual.toDual.{0}) →
    (∀ (a : Fin n), Eq.{1} (N a a) 1) →
      Matrix.BlockTriangular.{0, 0, 0} N' (DFunLike.coe.{1, 1, 1} OrderDual.toDual.{0}) →
        (∀ (a : Fin n), Eq.{1} (N' a a) 1) →
          Matrix.BlockTriangular.{0, 0, 0} U id.{1} →
            Matrix.BlockTriangular.{0, 0, 0} U' id.{1} →
              Ne.{1} (Matrix.det.{0, 0} U') 0 →
                Eq.{1} (HMul.hMul.{0, 0, 0} N U) (HMul.hMul.{0, 0, 0} N' U') → And (Eq.{1} N N') (Eq.{1} U U') := by
  intro n N N' U U' hN hNd hN' hN'd hU hU' hdet hEq
  have hdN : N.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular N hN]
    exact Finset.prod_eq_one (fun i _ => hNd i)
  have hdN' : N'.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular N' hN']
    exact Finset.prod_eq_one (fun i _ => hN'd i)
  have hdU : U.det ≠ 0 := by
    have h := congrArg Matrix.det hEq
    rw [Matrix.det_mul, Matrix.det_mul, hdN, hdN', one_mul, one_mul] at h
    rw [h]
    exact hdet
  have uN' : IsUnit N'.det := by rw [hdN']; exact isUnit_one
  have uN : IsUnit N.det := by rw [hdN]; exact isUnit_one
  have uU : IsUnit U.det := isUnit_iff_ne_zero.mpr hdU
  let _ : Invertible N' := Matrix.invertibleOfIsUnitDet N' uN'
  let _ : Invertible U := Matrix.invertibleOfIsUnitDet U uU
  have hAeq : N'⁻¹ * N = U' * U⁻¹ := by
    calc N'⁻¹ * N = N'⁻¹ * N * (U * U⁻¹) := by
          rw [Matrix.mul_nonsing_inv U uU, Matrix.mul_one]
      _ = N'⁻¹ * (N * U) * U⁻¹ := by simp only [Matrix.mul_assoc]
      _ = N'⁻¹ * (N' * U') * U⁻¹ := by rw [hEq]
      _ = U' * U⁻¹ := by
          rw [← Matrix.mul_assoc N'⁻¹, Matrix.nonsing_inv_mul N' uN', Matrix.one_mul]
  have hAl : (N'⁻¹ * N).BlockTriangular (DFunLike.coe OrderDual.toDual) :=
    (Matrix.blockTriangular_inv_of_blockTriangular hN').mul hN
  have hAu : (N'⁻¹ * N).BlockTriangular id := by
    rw [hAeq]
    exact hU'.mul (Matrix.blockTriangular_inv_of_blockTriangular hU)
  have hoff : ∀ i j, i ≠ j → (N'⁻¹ * N) i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hAl (OrderDual.toDual_lt_toDual.mpr h)
    · exact hAu h
  have hNA : N = N' * (N'⁻¹ * N) := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv N' uN', Matrix.one_mul]
  have hdiag : ∀ i, (N'⁻¹ * N) i i = 1 := by
    intro i
    have h1 := congrFun (congrFun hNA i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · rw [hNd i, hN'd i, one_mul] at h1
      exact h1.symm
    · intro k _ hk
      rw [hoff k i hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hA1 : N'⁻¹ * N = 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      rw [hdiag, Matrix.one_apply_eq]
    · rw [hoff i j h, Matrix.one_apply_ne h]
  have hNN : N = N' := by rw [hNA, hA1, Matrix.mul_one]
  refine ⟨hNN, ?_⟩
  calc U = N⁻¹ * (N * U) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul N uN, Matrix.one_mul]
    _ = N⁻¹ * (N * U') := by rw [hEq, hNN]
    _ = U' := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul N uN, Matrix.one_mul]
end Bl.general_b_fact_form
