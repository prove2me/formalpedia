-- Prove2me | solution 1 for BSLambda.flipSet_apply_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:47:20.642803+00:00
-- url     : https://prove2.me/submissions/5e96f36d-e484-4d78-87f2-4e131ec29760

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]


theorem solution {x : Input V} {A : Finset V} {v : V} :
    flipSet x A v = x v ↔ v ∉ A := by
  by_cases h : v ∈ A <;> cases hv : x v <;> simp [flipSet, h, hv]
