-- Prove2me | solution 1 for BSLambda.iterBlock_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:35:53.906345+00:00
-- url     : https://prove2.me/submissions/8ca60286-2f3a-430c-bdc6-fb7300475098

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
variable {V ι : Type*} [DecidableEq V] {blk : ι → Finset V}
namespace BSLambda
theorem _root_.solution (hdisj : Pairwise (Disjoint on blk)) :
    ∀ m : ℕ, Pairwise (Disjoint on (iterBlock blk m))
  | 0 => fun t u h ↦ absurd (Subsingleton.elim (α := PUnit) t u) h
  | m + 1 => fun t u h ↦ Finset.disjoint_product.2 <|
      (em (t.1 = u.1)).symm.imp (fun h1 ↦ hdisj h1) fun h1 ↦
        solution hdisj m fun h2 ↦ h (Prod.ext (α := ι) (β := IterCoord ι m) h1 h2)
end BSLambda
