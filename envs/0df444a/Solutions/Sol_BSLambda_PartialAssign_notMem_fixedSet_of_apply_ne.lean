-- Prove2me | solution 1 for BSLambda.PartialAssign.notMem_fixedSet_of_apply_ne
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:52:09.323582+00:00
-- url     : https://prove2.me/submissions/f3f1bb44-206e-49c4-9b4e-90105a38d88f

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


theorem solution {P : PartialAssign V} {x y : Input V} (hx : P.Sat x)
    (hy : P.Sat y) {v : V} (hne : x v ≠ y v) : v ∉ P.fixedSet := by
  intro hv
  cases e : P v with
  | none => simp [fixedSet,e] at hv
  | some b => exact hne ((hx v b e).trans (hy v b e).symm)
