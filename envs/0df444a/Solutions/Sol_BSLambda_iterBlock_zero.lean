-- Prove2me | solution 1 for BSLambda.iterBlock_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:47:26.592599+00:00
-- url     : https://prove2.me/submissions/7f48a6d8-8602-4067-8e00-b430938a18db

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
theorem _root_.solution {V ι : Type*} [DecidableEq V] (blk : ι → Finset V)
    (t : IterCoord ι 0) : iterBlock blk 0 t = (Finset.univ : Finset PUnit) := rfl
end BSLambda
