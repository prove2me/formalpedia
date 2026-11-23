-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.trunc_total
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:43.041123+00:00
-- url     : https://prove2.me/submissions/009df08a-48c4-4c6f-ad0a-04004fe81224

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_trunc_normal
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
theorem _root_.solution (x y : TruncK K' n) : x ∣ y ∨ y ∣ x := by
  obtain ⟨k, hk, u, hu, rfl⟩ := trunc_normal x
  obtain ⟨l, hl, v, hv, rfl⟩ := trunc_normal y
  rcases le_total k l with h | h
  · left
    refine ⟨hu.unit⁻¹ * v * (TT) ^ (l - k), ?_⟩
    rw [← Nat.add_sub_cancel' h, pow_add]
    simp only [Nat.add_sub_cancel_left]
    calc v * ((TT) ^ k * (TT) ^ (l - k)) = (u * hu.unit⁻¹) * v * (TT) ^ k * (TT) ^ (l - k) := by
          rw [IsUnit.mul_val_inv]; ring
      _ = _ := by ring
  · right
    refine ⟨hv.unit⁻¹ * u * (TT) ^ (k - l), ?_⟩
    rw [← Nat.add_sub_cancel' h, pow_add]
    simp only [Nat.add_sub_cancel_left]
    calc u * ((TT) ^ l * (TT) ^ (k - l)) = (v * hv.unit⁻¹) * u * (TT) ^ l * (TT) ^ (k - l) := by
          rw [IsUnit.mul_val_inv]; ring
      _ = _ := by ring
end Formalism.CyclotomicNorms.residueMatrixData
