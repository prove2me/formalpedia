-- Prove2me | solution 1 for BSLambda.sensAt_eq_card_univ
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:53:52.55468+00:00
-- url     : https://prove2.me/submissions/e164b4d8-4c9a-41fc-8d6a-eafd9162b249

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]


theorem solution {f : Input V → Bool} {x : Input V} (h : ∀ v, SensitiveCoord f x v) :
    sensAt f x = Fintype.card V := by
  simp [sensAt,sensCoords,h]
