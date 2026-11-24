-- Prove2me | solution 1 for BSLambda.CertFamily.lam_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:33:17.354791+00:00
-- url     : https://prove2.me/submissions/1eedd7b9-12bb-44b2-9df8-16dd5e209313

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_BSLambda_CertFamily_l2_opNorm_gram_le
public import Theorems.Thm_BSLambda_lam_sq_le_l2_opNorm_gram


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution : lam F.ind ^ 2 ≤ (F.c : ℝ) + 2 * F.offBound :=
  le_trans (lam_sq_le_l2_opNorm_gram F.ind) F.l2_opNorm_gram_le
end BSLambda.CertFamily
