-- Prove2me | solution 1 for BSLambda.flipSet_empty
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:47:17.3904+00:00
-- url     : https://prove2.me/submissions/498f29b9-7a75-4b2e-9f53-8bc9c9505c77

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]


theorem solution (x : Input V) : flipSet x ∅ = x := by
  funext v; simp [flipSet]
