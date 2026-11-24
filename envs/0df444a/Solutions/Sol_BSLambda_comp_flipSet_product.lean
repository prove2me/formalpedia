-- Prove2me | solution 1 for BSLambda.comp_flipSet_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:26.925822+00:00
-- url     : https://prove2.me/submissions/be5636dc-4204-48b3-9f6a-fcd9752b105d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Theorems.Thm_BSLambda_comp_apply
public import Theorems.Thm_BSLambda_iterBlock_zero
public import Theorems.Thm_BSLambda_iterFun_zero
public import Theorems.Thm_BSLambda_flipSet_zeroInput_product_slice
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.zeroInput_apply


attribute [local simp] BSLambda.iterBlock_zero
attribute [local simp] BSLambda.iterFun_zero

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u
namespace BSLambda
theorem _root_.solution {V W : Type*} [DecidableEq V] [DecidableEq W]
    {f : Input V → Bool} {g : Input W → Bool} {A : Finset V} {B : Finset W}
    (hzero : g (zeroInput W) = false) (hflip : g (flipSet (zeroInput W) B) = true) :
    comp f g (flipSet (zeroInput (V × W)) (A ×ˢ B)) = f (flipSet (zeroInput V) A) := by
  rw [comp_apply]
  congr 1
  funext v
  rw [flipSet_zeroInput_product_slice, flipSet_zeroInput_apply]
  by_cases hv : v ∈ A <;> simp [hv, hzero, hflip]
end BSLambda
