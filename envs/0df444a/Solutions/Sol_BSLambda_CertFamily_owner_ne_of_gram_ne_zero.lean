-- Prove2me | solution 1 for BSLambda.CertFamily.owner_ne_of_gram_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:23:19.925043+00:00
-- url     : https://prove2.me/submissions/1503908e-a6fa-49cc-b0b7-0503589cabba

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Theorems.Thm_BSLambda_CertFamily_gram_eq_zero_of_owner_eq

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
open BSLambda.CertFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {x y : Ones F.ind} (hxy : x ≠ y)
    (hne : gram F.ind x y ≠ 0) : F.owner x ≠ F.owner y :=
  fun h ↦ hne (F.gram_eq_zero_of_owner_eq hxy h)
end BSLambda.CertFamily
