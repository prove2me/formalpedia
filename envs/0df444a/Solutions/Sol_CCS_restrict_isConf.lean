-- Prove2me | solution 1 for CCS.restrict_isConf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:11:19.662404+00:00
-- url     : https://prove2.me/submissions/4a8663a3-83d7-4d14-9c2c-338470e52930

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Definitions.Def_EventStructures_CCS_Semantics
import Theorems.Thm_CCS_restrict_con
import Theorems.Thm_CCS_pmapSet_unres
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
theorem _root_.solution {E : SES (Action (Option Name))} {c : Set (restrict E).Event}
    (hc : (restrict E).toGES.isConf c) :
    E.toGES.isConf {y | ∃ hy, (⟨y, hy⟩ : (restrict E).Event) ∈ c} := by
  have h := GES.isConf_pmap (G := (restrict E).toGES) (H := E.toGES)
    (fun e => some e.1) (fun {s} h => (pmapSet_unres s) ▸ restrict_con (c := s) h)
    (fun {X u x} hX hu => by
      obtain ⟨Y, hY, hen⟩ := hX
      have hx : u.1 = x := by simpa using hu
      refine ⟨Y, fun y hy => ?_, hx ▸ hen⟩
      obtain ⟨hv, hm⟩ := hY y hy
      exact ⟨⟨y, hv⟩, hm, rfl⟩) hc
  rw [pmapSet_unres c] at h
  exact h
end CCS
