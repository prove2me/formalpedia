-- Prove2me | solution 2 for BSLambda.bsAt_le_bs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:14.01756+00:00
-- url     : https://prove2.me/submissions/15916e94-92de-4f61-a2da-c04f57157ca8

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) (x : Input V) : bsAt f x ≤ bs f :=
  Finset.le_sup (Finset.mem_univ x)
end BSLambda
