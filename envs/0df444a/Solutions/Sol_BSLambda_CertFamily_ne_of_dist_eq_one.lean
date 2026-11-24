-- Prove2me | solution 1 for BSLambda.CertFamily.ne_of_dist_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:22:34.09116+00:00
-- url     : https://prove2.me/submissions/84b66f4d-f556-4e9e-ba9e-98774def60fc

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Theorems.Thm_BSLambda_CertFamily_owner_sat
public import Theorems.Thm_BSLambda_PartialAssign_dist_eq_zero_iff
attribute [local simp] BSLambda.PartialAssign.dist_eq_zero_iff



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
open BSLambda.CertFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {x y : Ones F.ind} (hd : (F.P (F.owner y)).dist x.1 = 1) : x ≠ y := by
  rintro rfl
  rw [PartialAssign.dist_eq_zero_iff.2 (F.owner_sat x)] at hd
  omega
end BSLambda.CertFamily
