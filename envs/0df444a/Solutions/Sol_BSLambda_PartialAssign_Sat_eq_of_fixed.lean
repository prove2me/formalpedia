-- Prove2me | solution 1 for BSLambda.PartialAssign.Sat.eq_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:47:54.651333+00:00
-- url     : https://prove2.me/submissions/f5460692-7ce3-49ff-996a-f8abd9cdcf5f

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
namespace Sat
theorem _root_.solution {P : PartialAssign V} {x : Input V} (hx : P.Sat x) {v : V} {b : Bool}
    (hv : P v = some b) : x v = b := hx v b hv
end Sat
end BSLambda.PartialAssign
