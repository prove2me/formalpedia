-- Prove2me | solution 1 for BSLambda.CertFamily.l2_opNorm_offMat_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:38.862745+00:00
-- url     : https://prove2.me/submissions/a6a9f5b4-7833-40e3-8d7d-ec350e06b20b

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_BSLambda_CertFamily_offMat_nonneg
public import Theorems.Thm_BSLambda_CertFamily_offMat_row_sum_le
public import Theorems.Thm_BSLambda_CertFamily_offMat_col_sum_le
public import Theorems.Thm_Matrix_l2_opNorm_le_sqrt_of_row_col_sums


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution : ‖F.offMat‖ ≤ F.offBound :=
  Matrix.l2_opNorm_le_sqrt_of_row_col_sums F.offMat F.offMat_nonneg F.offMat_row_sum_le
    F.offMat_col_sum_le
end BSLambda.CertFamily
