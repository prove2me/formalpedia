-- Prove2me | solution 1 for BSLambda.PartialAssign.dist_eq_card_violSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:48:08.982694+00:00
-- url     : https://prove2.me/submissions/8f17577e-cef7-4fa4-9bf7-81bb55b6abeb

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
namespace BSLambda.PartialAssign
theorem _root_.solution (P : PartialAssign V) (x : Input V) :
    P.dist x = (P.violSet x).card := rfl
end BSLambda.PartialAssign
