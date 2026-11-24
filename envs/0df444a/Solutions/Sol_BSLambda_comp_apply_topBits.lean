-- Prove2me | solution 1 for BSLambda.comp_apply_topBits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:27.438507+00:00
-- url     : https://prove2.me/submissions/b2e611e7-66e9-4c8f-b8d0-8c64af6e1d60

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*}
namespace BSLambda
theorem _root_.solution (f : Input W → Bool) (g : Input V → Bool) (x : Input (W × V)) :
    comp f g x = f (topBits g x) := rfl
end BSLambda
