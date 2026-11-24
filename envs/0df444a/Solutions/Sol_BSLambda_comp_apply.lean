-- Prove2me | solution 1 for BSLambda.comp_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:34:55.588043+00:00
-- url     : https://prove2.me/submissions/f5a07b61-f094-4539-a198-f3188c31aaf6

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
theorem _root_.solution {W V : Type*} (f : Input W → Bool) (g : Input V → Bool)
    (x : Input (W × V)) : comp f g x = f fun w ↦ g fun v ↦ x (w, v) := rfl
end BSLambda
