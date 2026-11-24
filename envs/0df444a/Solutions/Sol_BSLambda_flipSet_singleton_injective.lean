-- Prove2me | solution 1 for BSLambda.flipSet_singleton_injective
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:52:12.821409+00:00
-- url     : https://prove2.me/submissions/bdd66d6e-0f9b-445a-aa03-a42bde75f4aa

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]


theorem solution (x : Input V) :
    Function.Injective fun v : V ↦ flipSet x {v} := by
  intro i j h
  by_contra ne
  have eq := congrFun h i
  cases hv : x i <;> simp [flipSet,ne,hv] at eq
