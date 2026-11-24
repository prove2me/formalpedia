-- Prove2me | solution 1 for BSLambda.flipSet_apply_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:47:21.767187+00:00
-- url     : https://prove2.me/submissions/f4699191-29a5-4011-8d70-0706f44b1c50

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]


theorem solution {x : Input V} {A : Finset V} {v : V} (hv : v ∉ A) :
    flipSet x A v = x v := by
  simp [flipSet, hv]
