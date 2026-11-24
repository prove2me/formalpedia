-- Prove2me | solution 1 for BSLambda.CertFamily.offMat_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:24:32.168981+00:00
-- url     : https://prove2.me/submissions/a3f0ebb8-c187-4492-b30b-7cc0cd5e66a5

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_BSLambda_CertFamily_offMat_apply
public import Theorems.Thm_BSLambda_CertFamily_gram_le_one


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution (x y : Ones F.ind) : F.offMat x y ≤ 1 := by
  rw [F.offMat_apply]
  split_ifs with h
  · exact F.gram_le_one (ne_of_apply_ne F.owner h.1)
  · exact zero_le_one
end BSLambda.CertFamily
