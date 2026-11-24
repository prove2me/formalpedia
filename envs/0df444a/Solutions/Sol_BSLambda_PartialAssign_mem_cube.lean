-- Prove2me | solution 1 for BSLambda.PartialAssign.mem_cube
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:47:12.874529+00:00
-- url     : https://prove2.me/submissions/bbc193e8-1204-4b9e-9f17-e96cc4b4da0d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V] [DecidableEq V]


theorem solution {P : PartialAssign V} {x : Input V} : x ∈ P.cube ↔ P.Sat x := by
  simp [cube]
