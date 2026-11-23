-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.tt_linIndep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:43.613903+00:00
-- url     : https://prove2.me/submissions/fc2bd852-e787-49fe-b2ff-a82eae1a0ded

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
theorem _root_.solution : LinearIndependent K' (fun i : Fin n => (TT) ^ (i : ℕ)) := by
  have h := (pbT K' n).basis.linearIndependent
  have hd : (pbT K' n).dim = n := by simp [pbT]
  have e : ∀ i : Fin (pbT K' n).dim, (pbT K' n).basis i = (TT) ^ (i : ℕ) := by
    intro i; rw [PowerBasis.basis_eq_pow]; rfl
  have h2 : LinearIndependent K' (fun i : Fin (pbT K' n).dim => (TT) ^ (i : ℕ)) := by
    convert h using 1
    · funext i; exact (e i).symm
    all_goals rfl
  exact h2.comp (Fin.cast hd.symm) (Fin.cast_injective _)
end Formalism.CyclotomicNorms.residueMatrixData
