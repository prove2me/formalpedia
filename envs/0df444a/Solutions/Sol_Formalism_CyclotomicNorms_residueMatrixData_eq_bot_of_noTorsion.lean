-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.eq_bot_of_noTorsion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:56.649812+00:00
-- url     : https://prove2.me/submissions/33974be8-ca88-40b1-a6f0-2248ca49f965

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_tt_pow_n
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
theorem _root_.solution {a : ℕ} (N : Submodule (TruncK K' n) (Fin a → TruncK K' n))
    (h : ∀ x ∈ N, (TT) • x = 0 → x = 0) : N = ⊥ := by
  have key : ∀ m : ℕ, ∀ y ∈ N, (TT) ^ m • y = 0 → y = 0 := by
    intro m
    induction m with
    | zero => intro y _ hy; simpa using hy
    | succ m ih =>
      intro y hy h0
      apply ih y hy
      apply h _ (N.smul_mem _ hy)
      rw [← mul_smul, ← pow_succ']; exact h0
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]
  exact key n y hy (by rw [tt_pow_n, zero_smul])
end Formalism.CyclotomicNorms.residueMatrixData
