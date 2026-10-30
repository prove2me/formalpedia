-- Prove2me | solution 1 for DerivativeChainContinuation.diagonal_projection_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:15:58.883625+00:00
-- url     : https://prove2.me/submissions/ea41e0c5-d0cb-45d0-8ef4-4c459ffabd94

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_det_diagonal_add_rankOne
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


open DerivativeChainContinuation in
theorem solution {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ) :
    (diagonal a * centeringProjection n).charpoly =
      C (n : ℂ)⁻¹ * X * derivative (∏ i, (X-C (a i))) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.finite_range a).infinite_compl).mono
  intro z hz
  have hz' : ∀ i, z-a i ≠ 0 := by
    intro i hi
    exact hz ⟨i, (sub_eq_zero.mp hi).symm⟩
  change (diagonal a * centeringProjection n).charpoly.eval z = _
  rw [eval_charpoly]
  have hm : scalar (Fin n) z - diagonal a * centeringProjection n =
      diagonal (fun i => z-a i) + vecMulVec (fun i => a i/(n : ℂ)) (fun _ => 1) := by
    ext i j
    simp [centeringProjection, Matrix.mul_sub, Matrix.mul_one, Matrix.diagonal_mul,
      Matrix.sub_apply, Matrix.add_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.vecMulVec_apply, Matrix.of_apply, div_eq_mul_inv]
    split_ifs <;> ring
  rw [hm, det_diagonal_add_rankOne _ _ _ hz']
  simp only [one_mul, eval_mul, eval_C, eval_X, derivative_prod_finset,
    derivative_X_sub_C, mul_one, eval_finset_sum, eval_prod, eval_sub, eval_X, eval_C]
  have hs : 1 + (∑ i, a i/(n : ℂ)/(z-a i)) =
      (z/(n : ℂ)) * ∑ i, (z-a i)⁻¹ := by
    have he (i : Fin n) : a i/(n : ℂ)/(z-a i) =
        z/(n : ℂ)*(z-a i)⁻¹-(n : ℂ)⁻¹ := by
      field_simp [hz' i]
      ring
    simp only [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [hnC]
  rw [hs]
  have hp : (∏ i, (z-a i))*(∑ i, (z-a i)⁻¹) =
      ∑ i, ∏ j ∈ Finset.univ.erase i, (z-a j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    field_simp [hz' i]
  calc
    (∏ i, (z-a i))*(z/(n : ℂ)*(∑ i, (z-a i)⁻¹)) =
      ((n : ℂ)⁻¹*z)*((∏ i, (z-a i))*(∑ i, (z-a i)⁻¹)) := by ring
    _ = _ := by rw [hp]
