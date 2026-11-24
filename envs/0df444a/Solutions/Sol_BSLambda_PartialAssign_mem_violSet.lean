-- Prove2me | solution 1 for BSLambda.PartialAssign.mem_violSet
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:47:15.142599+00:00
-- url     : https://prove2.me/submissions/cbc42c40-c3ae-486b-9bb6-ded5d8bab3be

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V]


theorem solution {P : PartialAssign V} {x : Input V} {v : V} :
    v ∈ P.violSet x ↔ P v ≠ none ∧ P v ≠ some (x v) := by
  simp [violSet]
