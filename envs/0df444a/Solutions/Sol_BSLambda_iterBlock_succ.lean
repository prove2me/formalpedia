-- Prove2me | solution 1 for BSLambda.iterBlock_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:47.118181+00:00
-- url     : https://prove2.me/submissions/dd57a653-784f-41c8-b143-739fce9c2bba

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
theorem _root_.solution {V ι : Type*} [DecidableEq V] (blk : ι → Finset V) (m : ℕ)
    (t : IterCoord ι (m + 1)) : iterBlock blk (m + 1) t = blk t.1 ×ˢ iterBlock blk m t.2 := rfl
end BSLambda
