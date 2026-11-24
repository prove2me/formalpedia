-- Prove2me | solution 1 for BSLambda.Final.exists_ratio_blowup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:27.541276+00:00
-- url     : https://prove2.me/submissions/ea5d188d-9c21-4d8c-8669-8528509a56b6

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
public import Theorems.Thm_BSLambda_Final_bs_div_lam_sq_ge
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
    ∃ γ : Idx → Idx → Fin r, ∀ m : ℕ,
      (14011 / U) ^ m * lam (iterFun (ind Arc γ) m) ^ 2
        ≤ (bs (iterFun (ind Arc γ) m) : ℝ) := by
  obtain ⟨γ, h₁, h₂⟩ := exists_listOne_listTwo
  exact ⟨γ, bs_div_lam_sq_ge h₁ h₂⟩
end BSLambda.Final
