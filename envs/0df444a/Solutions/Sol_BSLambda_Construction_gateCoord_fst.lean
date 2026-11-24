-- Prove2me | solution 1 for BSLambda.Construction.gateCoord_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:46:59.268438+00:00
-- url     : https://prove2.me/submissions/da7f633f-cb96-4703-80e0-6bfbd11aafe9

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
theorem _root_.solution (γ : ι → ι → Fin r) (i j : ι) : (gateCoord γ i j).1 = j := rfl
end BSLambda.Construction
