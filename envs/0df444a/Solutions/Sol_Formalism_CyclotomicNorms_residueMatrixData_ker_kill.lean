-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.ker_kill
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:43.004785+00:00
-- url     : https://prove2.me/submissions/6ca2e4f5-e6f2-42af-bffe-ddc4db365e8e

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_zero
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_succ
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_succ_zero
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_succ_succ

set_option autoImplicit false
open Polynomial Matrix
open Formalism Formalism.CyclotomicNorms
noncomputable section
open Formalism.CyclotomicNorms.residueMatrixData
variable {K' : Type} [Field K'] {n : ℕ}
local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)
namespace Formalism.CyclotomicNorms.residueMatrixData
theorem _root_.solution {a : ℕ} (Φ P Q : Matrix (Fin a) (Fin a) (TruncK K' n)) (k : Fin a → ℕ)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (hD : P * Φ * Q = diagonal (fun i => (TT) ^ k i)) (m : ℕ) (hm : ∀ i, k i ≤ m)
    (y : Fin a → TruncK K' n) (hy : y ∈ LinearMap.ker (Matrix.toLin' Φ)) : (TT) ^ m • y = 0 := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hy
  have hz : diagonal (fun i => (TT) ^ k i) *ᵥ (Q⁻¹ *ᵥ y) = 0 := by
    rw [← hD, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hQ, Matrix.mul_one,
      ← mulVec_mulVec, hy, mulVec_zero]
  have hz' : (TT) ^ m • (Q⁻¹ *ᵥ y) = 0 := by
    funext i
    have := congrFun hz i
    rw [mulVec_diagonal, Pi.zero_apply] at this
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← Nat.sub_add_cancel (hm i), pow_add, mul_assoc, this, mul_zero]
  have hy' : y = Q *ᵥ (Q⁻¹ *ᵥ y) := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hQ, one_mulVec]
  rw [hy', ← mulVec_smul, hz', mulVec_zero]
end Formalism.CyclotomicNorms.residueMatrixData
