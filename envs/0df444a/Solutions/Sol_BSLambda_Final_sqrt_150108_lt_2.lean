-- Prove2me | solution 2 for BSLambda.Final.sqrt_150108_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:22.027872+00:00
-- url     : https://prove2.me/submissions/c013e792-b945-4d31-a2fd-5f38042d82bd

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
theorem _root_.solution : Real.sqrt 150108 < 387.5 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 387.5)]
  norm_num
end BSLambda.Final
