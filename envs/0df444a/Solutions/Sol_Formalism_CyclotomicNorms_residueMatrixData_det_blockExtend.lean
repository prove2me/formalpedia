-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.det_blockExtend
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:41.864802+00:00
-- url     : https://prove2.me/submissions/51aa7247-df49-4d88-bf3d-25b67e95464f

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
variable {R : Type*} [CommRing R]
namespace Formalism.CyclotomicNorms.residueMatrixData
theorem _root_.solution {a : ℕ} (P : Matrix (Fin a) (Fin a) R) : (ext1 P).det = P.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [blockExtend_zero_succ, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, blockExtend_zero_zero,
    Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  congr 1
end Formalism.CyclotomicNorms.residueMatrixData
