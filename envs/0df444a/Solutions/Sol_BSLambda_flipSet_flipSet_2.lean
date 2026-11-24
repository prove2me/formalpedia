-- Prove2me | solution 2 for BSLambda.flipSet_flipSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:50:13.303579+00:00
-- url     : https://prove2.me/submissions/7fa603dd-05a4-42d3-879a-1306c5592e08

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet_symmDiff
attribute [local simp] BSLambda.flipSet_empty

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]
namespace BSLambda
theorem _root_.solution (x : Input V) (A : Finset V) : flipSet (flipSet x A) A = x := by
  rw [flipSet_flipSet_symmDiff, symmDiff_self, Finset.bot_eq_empty, flipSet_empty]
end BSLambda
