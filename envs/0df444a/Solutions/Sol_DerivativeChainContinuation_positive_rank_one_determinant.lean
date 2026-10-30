-- Prove2me | solution 1 for DerivativeChainContinuation.positive_rank_one_determinant
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:18:32.909046+00:00
-- url     : https://prove2.me/submissions/1ad17f1c-2662-4fb5-a9ea-daa56f8edc12

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators ComplexOrder


theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (u : Fin n → ℂ) :
    ‖A.det‖ ≤ ‖(A+vecMulVec u (star u)).det‖ := by
  have hunit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have he : vecMulVec u (star u)=replicateCol Unit u*replicateRow Unit (star u) := by
    ext i j
    simp [Matrix.mul_apply,vecMulVec_apply]
  rw [he,det_add_replicateCol_mul_replicateRow hunit]
  rw [Matrix.det_unique (1+replicateRow Unit (star u)*A⁻¹*replicateCol Unit u),norm_mul]
  have hq : (1+replicateRow Unit (star u)*A⁻¹*replicateCol Unit u : Matrix Unit Unit ℂ) () () =
      1+star u ⬝ᵥ (A⁻¹*ᵥu) := by
    simp [Matrix.mul_apply,Matrix.mulVec,dotProduct,Matrix.replicateCol_apply,Matrix.replicateRow_apply,
      Finset.mul_sum,Matrix.one_apply,Finset.sum_mul,mul_assoc]
    exact Finset.sum_comm
  rw [hq]
  have hnonneg := hA.inv.posSemidef.dotProduct_mulVec_nonneg u
  have hre : 0 ≤ (star u ⬝ᵥ (A⁻¹*ᵥu)).re := hA.inv.posSemidef.re_dotProduct_nonneg u
  have hnorm : 1 ≤ ‖1+star u ⬝ᵥ (A⁻¹*ᵥu)‖ := by
    rw [← Complex.re_eq_norm.mpr (add_nonneg zero_le_one hnonneg),Complex.add_re,Complex.one_re]
    linarith
  exact le_mul_of_one_le_right (norm_nonneg _) hnorm
