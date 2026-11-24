-- Prove2me | solution 1 for BSLambda.Final.lam_sq_lt_bs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:43:01.780809+00:00
-- url     : https://prove2.me/submissions/c0490750-cde4-445b-adca-b6c6961eeb02

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
public import Theorems.Thm_BSLambda_Final_bs_ge_real
public import Theorems.Thm_BSLambda_Final_lam_sq_le
public import Theorems.Thm_BSLambda_Final_U_lt
public import Theorems.Thm_BSLambda_CertFamily_lam_sq_le


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}
namespace BSLambda.Final
theorem _root_.solution (h₁ : ListOne γ) (h₂ : ListTwo γ) :
    lam (ind Arc γ) ^ 2 < (bs (ind Arc γ) : ℝ) := by
  linarith [lam_sq_le h₁ h₂, U_lt, bs_ge_real (γ := γ)]
end BSLambda.Final
