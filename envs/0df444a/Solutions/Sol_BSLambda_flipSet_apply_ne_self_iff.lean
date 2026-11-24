-- Prove2me | solution 1 for BSLambda.flipSet_apply_ne_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:51:07.061589+00:00
-- url     : https://prove2.me/submissions/50aba765-d41c-4f28-83d7-2c21d183cc93

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Theorems.Thm_BSLambda_zeroInput_apply
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.zeroInput_apply
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]
namespace BSLambda
theorem _root_.solution {x : Input V} {A : Finset V} {v : V} :
    flipSet x A v ≠ x v ↔ v ∈ A := by
  simp
end BSLambda
