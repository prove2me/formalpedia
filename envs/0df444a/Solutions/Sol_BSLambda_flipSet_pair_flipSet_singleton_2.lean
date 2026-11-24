-- Prove2me | solution 2 for BSLambda.flipSet_pair_flipSet_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:39.820817+00:00
-- url     : https://prove2.me/submissions/4dfa96c2-c42e-446f-af5d-b13d0f0b0095

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_singleton_flipSet_singleton
attribute [local simp] BSLambda.flipSet_flipSet

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]
namespace BSLambda
theorem _root_.solution (x : Input V) {p q : V} (hpq : p ≠ q) :
    flipSet (flipSet x {p, q}) {q} = flipSet x {p} := by
  rw [← flipSet_singleton_flipSet_singleton x hpq, flipSet_flipSet]
end BSLambda
