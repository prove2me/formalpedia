-- Prove2me | solution 1 for BSLambda.PartialAssign.Sat.flipSet_singleton
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:53:55.310862+00:00
-- url     : https://prove2.me/submissions/daa5ce44-d06a-4031-b017-483cf478be27

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


theorem solution {P : PartialAssign V} {x : Input V} (hx : P.Sat x) {v : V}
    (hv : v ∉ P.fixedSet) : P.Sat (flipSet x {v}) := by
  intro w b hw
  by_cases he : w = v
  · subst w; exact False.elim (hv (by simp [fixedSet,hw]))
  · simpa [flipSet,he] using hx w b hw
