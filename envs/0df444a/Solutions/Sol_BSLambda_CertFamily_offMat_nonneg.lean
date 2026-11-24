-- Prove2me | solution 1 for BSLambda.CertFamily.offMat_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:23:16.851932+00:00
-- url     : https://prove2.me/submissions/f5ec7e3a-248f-42f3-afa4-ffd64928cdb7

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_BSLambda_CertFamily_offMat_apply
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
theorem _root_.solution (x y : Ones F.ind) : 0 ≤ F.offMat x y := by
  rw [F.offMat_apply]
  split_ifs
  exacts [gram_nonneg F.ind x y, le_rfl]
end BSLambda.CertFamily
