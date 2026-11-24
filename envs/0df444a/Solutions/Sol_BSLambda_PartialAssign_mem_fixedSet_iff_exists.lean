-- Prove2me | solution 1 for BSLambda.PartialAssign.mem_fixedSet_iff_exists
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:49:26.086181+00:00
-- url     : https://prove2.me/submissions/c375dbab-e933-47c0-9f6e-e6ec1dea4cc2

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
    v ∈ P.fixedSet ↔ ∃ b, P v = some b := by
  cases hv : P v <;> simp [fixedSet,hv]
