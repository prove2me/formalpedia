-- Prove2me | solution 1 for BSLambda.sensAt_le_card
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:53:53.512272+00:00
-- url     : https://prove2.me/submissions/888d1a53-71f8-4cee-b29e-467c79b3d416

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]


theorem solution {f : Input V → Bool} {x : Input V} {s : Finset V}
    (h : sensCoords f x ⊆ s) : sensAt f x ≤ s.card := by
  exact Finset.card_le_card h
