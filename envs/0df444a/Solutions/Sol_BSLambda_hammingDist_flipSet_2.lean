-- Prove2me | solution 2 for BSLambda.hammingDist_flipSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:56:20.361557+00:00
-- url     : https://prove2.me/submissions/86d8be3e-21fd-4dc9-bae9-042df342ccbc

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Theorems.Thm_BSLambda_zeroInput_apply
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_ne_self_iff
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
attribute [local simp] BSLambda.zeroInput_apply
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (x : Input V) (A : Finset V) :
    hammingDist x (flipSet x A) = A.card := by
  simp only [hammingDist, ne_comm (a := x _), flipSet_apply_ne_self_iff,
    Finset.filter_mem_eq_inter, Finset.univ_inter]
end BSLambda
