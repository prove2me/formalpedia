-- Prove2me | solution 1 for BSLambda.flipSet_zeroInput_product_slice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:35:39.603112+00:00
-- url     : https://prove2.me/submissions/1c2b4ec9-544f-4565-a730-d9142ff7e22f

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Theorems.Thm_BSLambda_iterBlock_zero
public import Theorems.Thm_BSLambda_iterFun_zero
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
    (A : Finset V) (B : Finset W) (v : V) :
    (fun w => flipSet (zeroInput (V × W)) (A ×ˢ B) (v, w))
      = if v ∈ A then flipSet (zeroInput W) B else zeroInput W := by
  funext w
  by_cases hv : v ∈ A <;> simp [zeroInput, Finset.mem_product, hv]
end BSLambda
