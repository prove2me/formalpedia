-- Prove2me | solution 2 for BSLambda.flipSet_singleton_flipSet_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:13.429496+00:00
-- url     : https://prove2.me/submissions/ca14975a-9e40-4ae7-a86a-93b3ef0c336f

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Theorems.Thm_Finset_symmDiff_singleton_singleton
public import Theorems.Thm_BSLambda_flipSet_flipSet_symmDiff

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]
namespace BSLambda
theorem _root_.solution (x : Input V) {p q : V} (hpq : p ≠ q) :
    flipSet (flipSet x {p}) {q} = flipSet x {p, q} := by
  rw [flipSet_flipSet_symmDiff, Finset.symmDiff_singleton_singleton hpq]
end BSLambda
