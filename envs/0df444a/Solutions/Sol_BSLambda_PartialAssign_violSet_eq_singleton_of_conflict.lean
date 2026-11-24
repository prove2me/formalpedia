-- Prove2me | solution 1 for BSLambda.PartialAssign.violSet_eq_singleton_of_conflict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:09:45.019677+00:00
-- url     : https://prove2.me/submissions/838ffbbf-8e95-42b6-8f78-4f1d8846485a

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet
public import Theorems.Thm_BSLambda_PartialAssign_violSet_subset_fixedSet
public import Theorems.Thm_BSLambda_PartialAssign_violSet_subset_of_sat_of_eq_off
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_mem_violSet
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
variable [Fintype V] [DecidableEq V]
namespace BSLambda.PartialAssign
theorem _root_.solution {P Q : PartialAssign V} {x : Input V} {p q : V}
    (hx : P.Sat x) (hy : Q.Sat (flipSet x {p, q})) (hc : P.Conflict Q q)
    (hp : p ∉ Q.fixedSet) : Q.violSet x = {q} := by
  have hsub : Q.violSet x ⊆ {p, q} :=
    violSet_subset_of_sat_of_eq_off hy fun _ hv ↦ (flipSet_apply_of_notMem hv).symm
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨hc.mem_violSet hx, fun v hv ↦ ?_⟩
  rcases Finset.mem_insert.1 (hsub hv) with rfl | h
  · exact absurd (violSet_subset_fixedSet _ _ hv) hp
  · exact Finset.mem_singleton.1 h
end BSLambda.PartialAssign
