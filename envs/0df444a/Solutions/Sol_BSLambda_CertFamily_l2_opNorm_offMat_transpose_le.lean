-- Prove2me | solution 1 for BSLambda.CertFamily.l2_opNorm_offMat_transpose_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:30:56.054037+00:00
-- url     : https://prove2.me/submissions/8a713db1-1b8d-4f86-9dd6-65ff7ed464ed

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_BSLambda_CertFamily_l2_opNorm_offMat_le
public import Theorems.Thm_Matrix_l2_opNorm_transpose


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution : ‖F.offMatᵀ‖ ≤ F.offBound :=
  F.offMat.l2_opNorm_transpose.trans_le F.l2_opNorm_offMat_le
end BSLambda.CertFamily
