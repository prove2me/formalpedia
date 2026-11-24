-- Prove2me | solution 1 for BSLambda.Final.exists_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:26.682872+00:00
-- url     : https://prove2.me/submissions/76716e10-bf02-4bec-97e0-8e6385d9272f

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
public import Theorems.Thm_BSLambda_Final_bs_ge
public import Theorems.Thm_BSLambda_Final_bs_ge_real
public import Theorems.Thm_BSLambda_Final_lam_sq_le
public import Theorems.Thm_BSLambda_Final_lam_rpow_le
public import Theorems.Thm_BSLambda_Final_exists_listOne_listTwo
public import Theorems.Thm_BSLambda_CertFamily_lam_sq_le


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}
namespace BSLambda.Final
theorem _root_.solution :
    ∃ γ : Idx → Idx → Fin r,
      14011 ≤ bs (ind Arc γ) ∧ lam (ind Arc γ) ^ 2 ≤ U ∧
        lam (ind Arc γ) ^ alpha ≤ (bs (ind Arc γ) : ℝ) := by
  obtain ⟨γ, h₁, h₂⟩ := exists_listOne_listTwo
  exact ⟨γ, bs_ge, lam_sq_le h₁ h₂, (lam_rpow_le h₁ h₂).trans bs_ge_real⟩
end BSLambda.Final
