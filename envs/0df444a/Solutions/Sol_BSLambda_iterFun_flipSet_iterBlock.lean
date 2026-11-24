-- Prove2me | solution 1 for BSLambda.iterFun_flipSet_iterBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:14.291445+00:00
-- url     : https://prove2.me/submissions/b5058b28-6666-4a19-a7d9-cb9e1ea900e3

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Theorems.Thm_BSLambda_iterBlock_zero
public import Theorems.Thm_BSLambda_iterFun_zero
public import Theorems.Thm_BSLambda_comp_flipSet_product
public import Theorems.Thm_BSLambda_iterFun_zeroInput
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
variable {V ι : Type*} [DecidableEq V] {f : Input V → Bool} {blk : ι → Finset V}
namespace BSLambda
theorem _root_.solution (hzero : f (zeroInput V) = false)
    (hflip : ∀ i, f (flipSet (zeroInput V) (blk i)) = true) :
    ∀ (m : ℕ) (t : IterCoord ι m),
      iterFun f m (flipSet (zeroInput (IterCoord V m)) (iterBlock blk m t)) = true
  | 0 => fun _ ↦ by
      change flipSet (zeroInput PUnit) Finset.univ PUnit.unit = true
      simp
  | m + 1 => fun t ↦
      (comp_flipSet_product (iterFun_zeroInput hzero m)
        (solution hzero hflip m t.2)).trans (hflip t.1)
end BSLambda
