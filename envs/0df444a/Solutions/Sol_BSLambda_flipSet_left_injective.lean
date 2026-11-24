-- Prove2me | solution 1 for BSLambda.flipSet_left_injective
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:52:18.870112+00:00
-- url     : https://prove2.me/submissions/80d1e19e-d014-40c4-afb0-ce7577867069

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]


theorem solution (A : Finset V) : Function.Injective (flipSet · A) := by
  intro x y e; funext v
  have eq := congrFun e v
  by_cases h : v ∈ A <;> simpa [flipSet,h] using eq
