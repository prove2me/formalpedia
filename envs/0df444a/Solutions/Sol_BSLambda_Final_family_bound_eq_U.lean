-- Prove2me | solution 1 for BSLambda.Final.family_bound_eq_U
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:57.149054+00:00
-- url     : https://prove2.me/submissions/896e8e76-9fe1-4500-92b0-798308192b08

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}
namespace BSLambda.Final
theorem _root_.solution (h₁ : ListOne γ) (h₂ : ListTwo γ) :
    ((family γ h₁ h₂).c : ℝ) + 2 * (family γ h₁ h₂).offBound = U := by
  rw [CertFamily.offBound, U, family_c, family_A, family_B]
  norm_num
end BSLambda.Final
