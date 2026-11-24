-- Prove2me | solution 2 for BSLambda.Construction.gateCoord_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:52:39.688561+00:00
-- url     : https://prove2.me/submissions/0c9e3332-444a-491c-aeee-2969af680515

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
namespace BSLambda.Construction
theorem _root_.solution (γ : ι → ι → Fin r) (i : ι) :
    Function.Injective (gateCoord γ i) := fun _ _ h ↦ congrArg Prod.fst h
end BSLambda.Construction
