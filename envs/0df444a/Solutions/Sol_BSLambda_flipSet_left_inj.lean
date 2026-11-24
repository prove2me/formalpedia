-- Prove2me | solution 1 for BSLambda.flipSet_left_inj
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:47:19.619314+00:00
-- url     : https://prove2.me/submissions/5d5c06cf-d8c9-4ba5-b456-6755eb8622e1

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]


theorem solution {x y : Input V} {A : Finset V} :
    flipSet x A = flipSet y A ↔ x = y := by
  constructor
  · intro h; funext v
    have hv := congrFun h v
    by_cases hv' : v ∈ A <;> simpa [flipSet, hv'] using hv
  · rintro rfl; rfl
