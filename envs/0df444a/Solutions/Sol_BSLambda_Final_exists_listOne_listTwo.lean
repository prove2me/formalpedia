-- Prove2me | solution 1 for BSLambda.Final.exists_listOne_listTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:00.560811+00:00
-- url     : https://prove2.me/submissions/b6edec40-72c4-4825-8448-e479f0d9f4a2

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
public import Theorems.Thm_BSLambda_Final_card_idx
public import Theorems.Thm_BSLambda_LLL_exists_gate_labelling


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}
namespace BSLambda.Final
theorem _root_.solution : ∃ γ : Idx → Idx → Fin r, ListOne γ ∧ ListTwo γ :=
  LLL.exists_gate_labelling (Arc := Arc) (r := r) card_idx isDR_arc rfl
end BSLambda.Final
