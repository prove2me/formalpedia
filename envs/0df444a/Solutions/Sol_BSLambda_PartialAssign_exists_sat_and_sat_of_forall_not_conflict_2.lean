-- Prove2me | solution 2 for BSLambda.PartialAssign.exists_sat_and_sat_of_forall_not_conflict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:09:30.518891+00:00
-- url     : https://prove2.me/submissions/75d556b6-c871-4b36-9251-9c3a57b2a569

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Theorems.Thm_BSLambda_PartialAssign_proj_apply
public import Theorems.Thm_BSLambda_PartialAssign_proj_sat
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


attribute [local simp] BSLambda.PartialAssign.proj_apply
attribute [local simp] BSLambda.PartialAssign.proj_sat

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
namespace BSLambda.PartialAssign
theorem _root_.solution {P Q : PartialAssign V}
    (h : ∀ v, ¬ P.Conflict Q v) : ∃ x : Input V, P.Sat x ∧ Q.Sat x := by
  refine ⟨P.proj fun v ↦ (Q v).getD false, P.proj_sat _, fun v b hb ↦ ?_⟩
  cases hP : P v with
  | none => simp [hP, hb]
  | some c =>
    simp only [proj_apply, hP, Option.getD_some]
    by_contra hne
    refine h v ⟨c, hP, ?_⟩
    cases b <;> simp_all
end BSLambda.PartialAssign
