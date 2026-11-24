-- Prove2me | solution 1 for BSLambda.CertFamily.l2_opNorm_gram_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:31:55.796242+00:00
-- url     : https://prove2.me/submissions/9a6d4573-5416-45be-83bf-06d0b8299972

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_BSLambda_CertFamily_gram_eq_add
public import Theorems.Thm_BSLambda_CertFamily_l2_opNorm_diagMat_le
public import Theorems.Thm_BSLambda_CertFamily_l2_opNorm_offMat_le
public import Theorems.Thm_BSLambda_CertFamily_l2_opNorm_offMat_transpose_le

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution : ‖gram F.ind‖ ≤ (F.c : ℝ) + 2 * F.offBound := by
  rw [F.gram_eq_add, two_mul, ← add_assoc]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add F.l2_opNorm_diagMat_le F.l2_opNorm_offMat_le))
    F.l2_opNorm_offMat_transpose_le)
end BSLambda.CertFamily
