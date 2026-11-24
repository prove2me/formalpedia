-- Prove2me | solution 1 for BSLambda.Final.ratio_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:57.865804+00:00
-- url     : https://prove2.me/submissions/6abc372e-1aac-4608-a04b-197c2f0d1ed6

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

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}
namespace BSLambda.Final
theorem _root_.solution : (1.768 : ℝ) < 14011 / U := by
  have h : (14011 : ℝ) / 7924 < 14011 / U := div_lt_div_of_pos_left (by norm_num) U_pos U_lt
  linarith
end BSLambda.Final
