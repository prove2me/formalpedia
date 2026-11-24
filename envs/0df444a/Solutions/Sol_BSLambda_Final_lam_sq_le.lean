-- Prove2me | solution 1 for BSLambda.Final.lam_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:05.567625+00:00
-- url     : https://prove2.me/submissions/11abe122-257a-41b7-befe-ff899224bb31

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
public import Theorems.Thm_BSLambda_Final_family_ind
public import Theorems.Thm_BSLambda_Final_family_bound_eq_U
public import Theorems.Thm_BSLambda_CertFamily_lam_sq_le


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}
namespace BSLambda.Final
theorem _root_.solution (h₁ : ListOne γ) (h₂ : ListTwo γ) : lam (ind Arc γ) ^ 2 ≤ U := by
  rw [← family_ind h₁ h₂, ← family_bound_eq_U h₁ h₂]
  exact (family γ h₁ h₂).lam_sq_le
end BSLambda.Final
