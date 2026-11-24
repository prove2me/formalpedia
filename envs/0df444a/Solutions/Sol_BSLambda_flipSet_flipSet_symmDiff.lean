-- Prove2me | solution 1 for BSLambda.flipSet_flipSet_symmDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:49:36.045672+00:00
-- url     : https://prove2.me/submissions/e00c12fd-8400-4c54-b880-070899a022a5

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Theorems.Thm_BSLambda_zeroInput_apply
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_empty
attribute [local simp] BSLambda.zeroInput_apply
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_empty

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]
namespace BSLambda
theorem _root_.solution (x : Input V) (A B : Finset V) :
    flipSet (flipSet x A) B = flipSet x (symmDiff A B) := by
  funext v
  by_cases hA : v ∈ A <;> by_cases hB : v ∈ B <;> simp [flipSet, hA, hB, Finset.mem_symmDiff]
end BSLambda
