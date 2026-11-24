-- Prove2me | solution 1 for BSLambda.flipSet_flipSet
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:47:22.724514+00:00
-- url     : https://prove2.me/submissions/4e318565-4f0d-4b8d-af79-029fd9e5cf4c

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]


theorem solution (x : Input V) (A : Finset V) : flipSet (flipSet x A) A = x := by
  funext v; by_cases h : v ∈ A <;> simp [flipSet, h]
