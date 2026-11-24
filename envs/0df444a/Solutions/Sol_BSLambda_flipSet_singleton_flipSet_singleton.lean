-- Prove2me | solution 1 for BSLambda.flipSet_singleton_flipSet_singleton
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:50:31.960385+00:00
-- url     : https://prove2.me/submissions/24517219-12f5-4d73-8f81-8fdabf65d438

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]


theorem solution (x : Input V) {p q : V} (hpq : p ≠ q) :
    flipSet (flipSet x {p}) {q} = flipSet x {p, q} := by
  funext v; by_cases h : v = p <;> by_cases e : v = q <;> simp_all [flipSet]
