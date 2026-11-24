-- Prove2me | solution 1 for BSLambda.iterFun_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:47:42.531694+00:00
-- url     : https://prove2.me/submissions/a9be7934-e359-407a-9f19-db225f03a96e

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u
namespace BSLambda
theorem _root_.solution {V : Type*} (f : Input V → Bool) (x : Input (IterCoord V 0)) :
    iterFun f 0 x = x PUnit.unit := rfl
end BSLambda
