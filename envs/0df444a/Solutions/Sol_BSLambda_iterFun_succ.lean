-- Prove2me | solution 1 for BSLambda.iterFun_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:53.869919+00:00
-- url     : https://prove2.me/submissions/b823606b-3d20-4c97-9628-6bb203c6418f

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
theorem _root_.solution {V : Type*} (f : Input V → Bool) (m : ℕ) :
    iterFun f (m + 1) = comp f (iterFun f m) := rfl
end BSLambda
