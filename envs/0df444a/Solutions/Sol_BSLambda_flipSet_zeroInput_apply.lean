-- Prove2me | solution 1 for BSLambda.flipSet_zeroInput_apply
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:47:18.371801+00:00
-- url     : https://prove2.me/submissions/54d2c3e4-887a-4c98-a275-a4d90ef6c706

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]


theorem solution (A : Finset V) (v : V) :
    flipSet (zeroInput V) A v = decide (v ∈ A) := by
  by_cases h : v ∈ A <;> simp [flipSet, zeroInput, h]
