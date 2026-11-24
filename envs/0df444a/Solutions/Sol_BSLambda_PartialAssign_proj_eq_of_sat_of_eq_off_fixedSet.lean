-- Prove2me | solution 1 for BSLambda.PartialAssign.proj_eq_of_sat_of_eq_off_fixedSet
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:53:58.956458+00:00
-- url     : https://prove2.me/submissions/086254f8-b75a-4f9d-8fa4-88c743e1ba9f

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
    (h : ∀ v ∉ P.fixedSet, y v = x v) : P.proj y = x := by
  funext v; cases e : P v with
  | none => simpa [proj,e] using h v (by simp [fixedSet,e])
  | some b => simpa [proj,e] using (hx v b e).symm
