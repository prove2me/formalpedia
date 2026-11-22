-- Prove2me | solution 1 for CCS.resid_pre_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:33.166641+00:00
-- url     : https://prove2.me/submissions/8e324cce-8ac4-4556-be2f-69738c23edcc

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
import Theorems.Thm_CCS_resid_nil
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
theorem _root_.solution {α : Action Name} {P : Process Name}
    {c : Set (semantics (.pre α P)).Event} (h : none ∉ c) :
    resid (.pre α P) c = .pre α P := by
  rw [resid]; simp [h]
end CCS
