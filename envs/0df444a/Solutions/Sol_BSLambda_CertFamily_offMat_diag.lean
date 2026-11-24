-- Prove2me | solution 1 for BSLambda.CertFamily.offMat_diag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:23:30.174664+00:00
-- url     : https://prove2.me/submissions/362d92e8-59b9-4e1b-802e-897e35b1c38d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_BSLambda_CertFamily_offMat_apply

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution (x : Ones F.ind) : F.offMat x x = 0 := by
  rw [F.offMat_apply, if_neg]
  exact fun h ↦ h.1 rfl
end BSLambda.CertFamily
