-- Prove2me | solution 1 for BSLambda.PartialAssign.proj_sat
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:47:16.366223+00:00
-- url     : https://prove2.me/submissions/b4bb9ccf-7d98-42fe-b9ba-09860abd1f73

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}


theorem solution (P : PartialAssign V) (x : Input V) : P.Sat (P.proj x) := by
  intro v b hv
  simp [proj, hv]
