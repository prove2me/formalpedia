-- Prove2me | solution 1 for BSLambda.CertFamily.sensAt_le_c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:22:15.307071+00:00
-- url     : https://prove2.me/submissions/b09157ad-5c54-48e3-9dda-adb45620e607

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Theorems.Thm_BSLambda_CertFamily_ind_eq_true_of_sat
public import Theorems.Thm_BSLambda_CertFamily_mem_fixedSet_of_ind_flipSet_singleton_eq_false
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
public import Theorems.Thm_BSLambda_PartialAssign_codim_eq_card_fixedSet
public import Theorems.Thm_BSLambda_mem_sensCoords
public import Theorems.Thm_BSLambda_sensAt_le_card


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
open BSLambda.CertFamily
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {i : ι} {x : Input V} (hx : (F.P i).Sat x) : sensAt F.ind x ≤ F.c := by
  rw [← F.codim_eq i, PartialAssign.codim_eq_card_fixedSet]
  exact sensAt_le_card fun v hv ↦ F.mem_fixedSet_of_ind_flipSet_singleton_eq_false hx
    (Bool.eq_false_iff.2 fun h ↦ mem_sensCoords.1 hv (h.trans (F.ind_eq_true_of_sat hx).symm))
end BSLambda.CertFamily
