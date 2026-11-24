-- Prove2me | solution 1 for BSLambda.CertFamily.ind_eq_true_of_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:16:53.041775+00:00
-- url     : https://prove2.me/submissions/3f82b455-454e-49f9-9c8a-a1c89df9d1f0

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_true_of_sat


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
open BSLambda.CertFamily
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {i : ι} {x : Input V} (h : (F.P i).Sat x) : F.ind x = true :=
  PartialAssign.indUnion_eq_true_of_sat h
end BSLambda.CertFamily
