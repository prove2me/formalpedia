-- Prove2me | solution 1 for BSLambda.PartialAssign.proj_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:45:17.121464+00:00
-- url     : https://prove2.me/submissions/2fe445bd-593d-4aa6-b512-7b4db5ac3d55

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
namespace BSLambda.PartialAssign
theorem _root_.solution (P : PartialAssign V) (x : Input V) (v : V) :
    P.proj x v = (P v).getD (x v) := rfl
end BSLambda.PartialAssign
