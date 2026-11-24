-- Prove2me | solution 1 for BSLambda.CertFamily.l2_opNorm_diagMat_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:23:59.81524+00:00
-- url     : https://prove2.me/submissions/c5362fef-7505-489c-b89b-8feee7a2f660

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_BSLambda_CertFamily_gram_diag_le
public import Theorems.Thm_BSLambda_gram_nonneg


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution : ‖F.diagMat‖ ≤ (F.c : ℝ) := by
  rw [diagMat, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun x ↦ ?_
  rw [Matrix.diag_apply, Real.norm_eq_abs, abs_of_nonneg (gram_nonneg F.ind x x)]
  exact F.gram_diag_le x
end BSLambda.CertFamily
