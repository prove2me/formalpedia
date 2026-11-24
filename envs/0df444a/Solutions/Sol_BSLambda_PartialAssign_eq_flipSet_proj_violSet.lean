-- Prove2me | solution 1 for BSLambda.PartialAssign.eq_flipSet_proj_violSet
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:53:54.503718+00:00
-- url     : https://prove2.me/submissions/1afa1b28-8cff-4475-a261-1e1b87b50dc3

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V] [DecidableEq V]


theorem solution (P : PartialAssign V) (x : Input V) :
    x = flipSet (P.proj x) (P.violSet x) := by
  funext v
  cases hp : P v with
  | none => simp [flipSet,violSet,proj,hp]
  | some b => cases b <;> cases hx : x v <;> simp [flipSet,violSet,proj,hp,hx]
