-- Prove2me | solution 1 for BSLambda.flipSet_pair_flipSet_singleton
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:52:15.239153+00:00
-- url     : https://prove2.me/submissions/d0380161-7796-4366-952f-4fc28c3851c9

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
    flipSet (flipSet x {p, q}) {q} = flipSet x {p} := by
  funext v; by_cases h : v = p <;> by_cases e : v = q <;> simp_all [flipSet]
