-- Prove2me | solution 1 for BSLambda.Final.exists_bs_gt_lam_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:26.146275+00:00
-- url     : https://prove2.me/submissions/c4895032-836c-4a3b-b189-3acdc5a0930e

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
public import Theorems.Thm_BSLambda_Final_lam_rpow_212_lt_bs
public import Theorems.Thm_BSLambda_Final_exists_listOne_listTwo

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}
namespace BSLambda.Final
theorem _root_.solution :
    ∃ f : Input (Coord Idx r) → Bool, lam f ^ (2.12 : ℝ) < (bs f : ℝ) := by
  obtain ⟨γ, h₁, h₂⟩ := exists_listOne_listTwo
  exact ⟨ind Arc γ, lam_rpow_212_lt_bs h₁ h₂⟩
end BSLambda.Final
