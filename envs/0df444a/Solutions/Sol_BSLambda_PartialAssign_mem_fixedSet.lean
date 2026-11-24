-- Prove2me | solution 1 for BSLambda.PartialAssign.mem_fixedSet
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:47:14.069206+00:00
-- url     : https://prove2.me/submissions/7f2be103-4bdf-4135-93bf-36f8aa752835

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


theorem solution {P : PartialAssign V} {v : V} :
    v ∈ P.fixedSet ↔ (P v).isSome := by
  simp [fixedSet]
