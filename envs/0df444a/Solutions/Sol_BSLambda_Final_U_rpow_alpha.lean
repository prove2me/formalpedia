-- Prove2me | solution 1 for BSLambda.Final.U_rpow_alpha
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:29.662493+00:00
-- url     : https://prove2.me/submissions/e419f9c4-5da7-4602-9627-a98e36bae76c

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
public import Theorems.Thm_BSLambda_Final_U_pos
public import Theorems.Thm_BSLambda_Final_log_U_pos

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}
namespace BSLambda.Final
theorem _root_.solution : U ^ (alpha / 2) = 14011 := by
  have h1 : alpha / 2 = Real.log 14011 / Real.log U := by
    rw [alpha]
    ring
  have h2 : Real.log U * (Real.log 14011 / Real.log U) = Real.log 14011 := by
    field_simp [log_U_pos.ne']
  rw [h1, Real.rpow_def_of_pos U_pos, h2]
  exact Real.exp_log (by norm_num)
end BSLambda.Final
