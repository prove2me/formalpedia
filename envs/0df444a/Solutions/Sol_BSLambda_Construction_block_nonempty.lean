-- Prove2me | solution 1 for BSLambda.Construction.block_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:52:24.163831+00:00
-- url     : https://prove2.me/submissions/3e490931-2f5a-4940-9d47-468d9a547c9d

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


theorem solution [NeZero r] (i : ι) : (block i : Finset (Coord ι r)).Nonempty := by
  exact ⟨(i,0), by simp [block]⟩
