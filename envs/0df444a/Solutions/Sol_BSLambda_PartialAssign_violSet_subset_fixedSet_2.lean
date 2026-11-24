-- Prove2me | solution 2 for BSLambda.PartialAssign.violSet_subset_fixedSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:04:05.545814+00:00
-- url     : https://prove2.me/submissions/d3a1fd92-60df-4145-a0bf-184869ec6a14

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet_iff_ne_none
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet
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


attribute [local simp] BSLambda.PartialAssign.mem_violSet

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V]
namespace BSLambda.PartialAssign
theorem _root_.solution (P : PartialAssign V) (x : Input V) :
    P.violSet x ⊆ P.fixedSet := fun _ hv ↦ mem_fixedSet_iff_ne_none.2 (mem_violSet.1 hv).1
end BSLambda.PartialAssign
