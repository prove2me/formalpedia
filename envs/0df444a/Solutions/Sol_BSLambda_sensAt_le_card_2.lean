-- Prove2me | solution 2 for BSLambda.sensAt_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:01.153564+00:00
-- url     : https://prove2.me/submissions/84a69c31-4ac4-43c2-9a4d-fc9da25d633a

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution {f : Input V → Bool} {x : Input V} {s : Finset V}
    (h : sensCoords f x ⊆ s) : sensAt f x ≤ s.card :=
  Finset.card_le_card h
end BSLambda
