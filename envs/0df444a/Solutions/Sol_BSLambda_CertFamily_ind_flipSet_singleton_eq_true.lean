-- Prove2me | solution 1 for BSLambda.CertFamily.ind_flipSet_singleton_eq_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:18:40.609367+00:00
-- url     : https://prove2.me/submissions/82547279-18c9-4985-af0d-fdc568d28c5d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Theorems.Thm_BSLambda_CertFamily_ind_eq_true_of_sat
public import Theorems.Thm_BSLambda_PartialAssign_Sat_flipSet_singleton


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
open BSLambda.CertFamily
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {i : ι} {x : Input V} (hx : (F.P i).Sat x) {p : V}
    (hp : p ∉ (F.P i).fixedSet) : F.ind (flipSet x {p}) = true :=
  F.ind_eq_true_of_sat (hx.flipSet_singleton hp)
end BSLambda.CertFamily
