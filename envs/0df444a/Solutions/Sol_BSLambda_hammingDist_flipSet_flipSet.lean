-- Prove2me | solution 1 for BSLambda.hammingDist_flipSet_flipSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:57:09.64626+00:00
-- url     : https://prove2.me/submissions/3819427a-5329-4315-89f3-92925975b07b

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Theorems.Thm_BSLambda_flipSet_flipSet_symmDiff
public import Theorems.Thm_BSLambda_hammingDist_flipSet
attribute [local simp] BSLambda.hammingDist_flipSet

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (x : Input V) (A B : Finset V) :
    hammingDist (flipSet x A) (flipSet x B) = (symmDiff A B).card := by
  have h : flipSet x B = flipSet (flipSet x A) (symmDiff A B) := by
    rw [flipSet_flipSet_symmDiff, symmDiff_symmDiff_cancel_left]
  rw [h, hammingDist_flipSet]
end BSLambda
