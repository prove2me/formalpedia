-- Prove2me | solution 1 for BSLambda.flipSet_singleton_self
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:52:18.097118+00:00
-- url     : https://prove2.me/submissions/a9dcd4c5-8d05-48bf-bcdd-6eaaf89ec52a

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]


theorem solution (x : Input V) (v : V) : flipSet x {v} v = !x v := by
  simp [flipSet]
