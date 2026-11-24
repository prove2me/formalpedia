-- Prove2me | solution 1 for BSLambda.CertFamily.mem_fixedSet_of_ind_flipSet_singleton_eq_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:19:47.414442+00:00
-- url     : https://prove2.me/submissions/47b487d4-9038-4308-aefd-5fa8b7a18212

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Theorems.Thm_BSLambda_CertFamily_ind_flipSet_singleton_eq_true

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
open BSLambda.CertFamily
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {i : ι} {x : Input V}
    (hx : (F.P i).Sat x) {p : V} (hp : F.ind (flipSet x {p}) = false) :
    p ∈ (F.P i).fixedSet := by
  by_contra hc
  rw [F.ind_flipSet_singleton_eq_true hx hc] at hp
  exact Bool.noConfusion hp
end BSLambda.CertFamily
