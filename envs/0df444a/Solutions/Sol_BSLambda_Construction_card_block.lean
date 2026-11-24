-- Prove2me | solution 1 for BSLambda.Construction.card_block
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:48:28.135827+00:00
-- url     : https://prove2.me/submissions/d36e0ff3-e1e8-45ac-8896-a139bb3c7245

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


theorem solution (i : ι) : (block i : Finset (Coord ι r)).card = r := by
  simp [block]
