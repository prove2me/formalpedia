-- Prove2me | solution 1 for BSLambda.Construction.gateCoord_injective
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:52:24.965666+00:00
-- url     : https://prove2.me/submissions/c6e2cad1-0858-4503-8c8d-8cc93c473e4e

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}


theorem solution (γ : ι → ι → Fin r) (i : ι) :
    Function.Injective (gateCoord γ i) := by
  intro j k h; exact congrArg Prod.fst h
