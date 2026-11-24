-- Prove2me | solution 1 for BSLambda.Final.two_lt_alpha
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:30.533856+00:00
-- url     : https://prove2.me/submissions/2511a355-0c36-40f7-9742-6625ef9a6844

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
public import Theorems.Thm_BSLambda_Final_U_lt
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
theorem _root_.solution : 2 < alpha := by
  have hlog : Real.log U < Real.log 14011 := Real.log_lt_log U_pos (U_lt.trans (by norm_num))
  rw [alpha, lt_div_iff₀ log_U_pos]
  linarith
end BSLambda.Final
