-- Prove2me | solution 1 for BSLambda.isSensitiveBlock_of_eq_true
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:52:06.897975+00:00
-- url     : https://prove2.me/submissions/38f5885b-c282-4b8e-9e42-7a099aba35a4

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]


theorem solution {f : Input V → Bool} {x : Input V} {A : Finset V}
    (hA : A.Nonempty) (hx : f x = false) (hflip : f (flipSet x A) = true) :
    IsSensitiveBlock f x A := by
  exact ⟨hA, by simp [hx,hflip]⟩
