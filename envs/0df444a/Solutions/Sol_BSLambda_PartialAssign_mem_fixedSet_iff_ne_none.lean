-- Prove2me | solution 1 for BSLambda.PartialAssign.mem_fixedSet_iff_ne_none
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:50:30.641213+00:00
-- url     : https://prove2.me/submissions/011db37b-1811-4e65-befe-16d4b8212e9f

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


theorem solution {P : PartialAssign V} {v : V} : v ∈ P.fixedSet ↔ P v ≠ none := by
  cases hv : P v <;> simp [fixedSet,hv]
