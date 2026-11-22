-- Prove2me | solution 1 for CCS.resid_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:56:23.807029+00:00
-- url     : https://prove2.me/submissions/0c108846-7e71-4183-9a9e-d7ba0c88e98b

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
import Theorems.Thm_CCS_resid_nil
import Theorems.Thm_CCS_resid_pre_neg
import Theorems.Thm_CCS_resid_sum_none
import Theorems.Thm_CCS_resid_par
import Theorems.Thm_CCS_resid_res
import Theorems.Thm_CCS_Action_strip_map
import Theorems.Thm_CCS_Label_co_co
import Theorems.Thm_CCS_Label_strip_map
import Theorems.Thm_GES_toFamily_Config
import Theorems.Thm_GES_toFamily_Event
import Theorems.Thm_PES_enables_iff
import Theorems.Thm_PES_toFamily_Config
import Theorems.Thm_PES_toFamily_Event
import Theorems.Thm_SES_toFamily_Config
attribute [local simp] CCS.Action.strip_map
attribute [local simp] CCS.Label.co_co
attribute [local simp] CCS.Label.strip_map
attribute [local simp] GES.toFamily_Config
attribute [local simp] GES.toFamily_Event
attribute [local simp] PES.enables_iff
attribute [local simp] PES.toFamily_Config
attribute [local simp] PES.toFamily_Event
attribute [local simp] SES.toFamily_Config


attribute [local simp] CCS.resid_nil

set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}
namespace CCS
theorem _root_.solution : ∀ {Name : Type u} (P : Process Name), resid P ∅ = P
  | _, .nil => rfl
  | _, .pre α P => resid_pre_neg (by simp)
  | _, .sum P Q => resid_sum_none (by simp) (by simp)
  | _, .par P Q => by
      rw [resid_par]
      have hL : projL (∅ : Set (semantics (.par P Q)).Event) = ∅ := by
        ext e; constructor
        · rintro ⟨u, hu, -⟩; exact hu
        · exact fun h => h.elim
      have hR : projR (∅ : Set (semantics (.par P Q)).Event) = ∅ := by
        ext f; constructor
        · rintro ⟨u, hu, -⟩; exact hu
        · exact fun h => h.elim
      rw [hL, hR, solution P, solution Q]
  | _, .res P => by
      rw [resid_res]
      have h : unres (∅ : Set (semantics (.res P)).Event) = ∅ := by
        ext y; constructor
        · rintro ⟨h, hm⟩; exact hm
        · exact fun h => h.elim
      rw [h, solution P]
end CCS
