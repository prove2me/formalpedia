-- Prove2me | solution 1 for BSLambda.ne_flipSet_apply
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:50:33.607263+00:00
-- url     : https://prove2.me/submissions/39d6a130-d748-4ed8-b7a4-6aa1cf8f6b78

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]


theorem solution {x : Input V} {A : Finset V} {v : V} (hv : v ∈ A) :
    x v ≠ flipSet x A v := by
  cases h : x v <;> simp [flipSet,hv,h]
