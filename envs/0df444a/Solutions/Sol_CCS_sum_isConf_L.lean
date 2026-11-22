-- Prove2me | solution 1 for CCS.sum_isConf_L
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:11:14.145421+00:00
-- url     : https://prove2.me/submissions/ce07b41e-b550-4584-acf3-6de10e421d80

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Definitions.Def_EventStructures_CCS_Semantics
import Theorems.Thm_CCS_pmapSet_inl
import Theorems.Thm_CCS_sum_con_L
import Theorems.Thm_CCS_Action_strip_map
import Theorems.Thm_CCS_Label_co_co
import Theorems.Thm_CCS_Label_strip_map
import Theorems.Thm_GES_isConf_pmap
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



set_option autoImplicit true
open PES Configuration ConfFamily
open CCS
variable {Name : Type*}
variable {Name : Type*}
variable {E F : SES (Action Name)} {α : Action Name}
namespace CCS
theorem _root_.solution {c : Set (E.Event ⊕ F.Event)}
    (hc : (sum E F).toGES.isConf c) : E.toGES.isConf {z | Sum.inl z ∈ c} := by
  refine (pmapSet_inl c) ▸ GES.isConf_pmap (G := (sum E F).toGES) (H := E.toGES) Sum.getLeft?
    (fun {s} h => (pmapSet_inl s) ▸ sum_con_L (c := s) h) (fun {X u x} hX hu => ?_) hc
  cases u with
  | inl z =>
    obtain ⟨Y, hY, hen⟩ := hX
    exact ⟨Y, fun y hy => ⟨Sum.inl y, hY y hy, rfl⟩, (by simpa using hu : z = x) ▸ hen⟩
  | inr z => exact absurd hu (by simp)
end CCS
