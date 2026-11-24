-- Prove2me | solution 1 for BSLambda.PartialAssign.mem_violSet_iff_exists_ne
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:49:23.836374+00:00
-- url     : https://prove2.me/submissions/6f68be52-6f90-4200-83c4-c12fa5a4666d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V]


theorem solution {P : PartialAssign V} {x : Input V} {v : V} :
    v ∈ P.violSet x ↔ ∃ b, P v = some b ∧ x v ≠ b := by
  cases hv : P v with
  | none => simp [violSet,hv]
  | some b => cases b <;> cases hx : x v <;> simp [violSet,hv,hx]
