-- Prove2me | solution 1 for BSLambda.Final.rpow_1_06_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:06.083621+00:00
-- url     : https://prove2.me/submissions/faf6ddd6-583e-4fb6-ad3e-ac388b9bb3c2

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
theorem _root_.solution : (7924 : ℝ) ^ (1.06 : ℝ) < 14011 := by
  refine lt_of_pow_lt_pow_left₀ 50 (by norm_num) ?_
  rw [← Real.rpow_natCast ((7924 : ℝ) ^ (1.06 : ℝ)) 50, ← Real.rpow_mul (by norm_num)]
  norm_num
end BSLambda.Final
