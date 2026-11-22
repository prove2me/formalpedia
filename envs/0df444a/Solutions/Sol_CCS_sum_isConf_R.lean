-- Prove2me | solution 1 for CCS.sum_isConf_R
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:11:38.212729+00:00
-- url     : https://prove2.me/submissions/240e77ba-4b68-4f4c-827c-e5a6038b0904

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Definitions.Def_EventStructures_CCS_Semantics
import Theorems.Thm_CCS_pmapSet_inr
import Theorems.Thm_CCS_sum_con_R
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
    (hc : (sum E F).toGES.isConf c) : F.toGES.isConf {z | Sum.inr z ∈ c} := by
  refine (pmapSet_inr c) ▸ GES.isConf_pmap (G := (sum E F).toGES) (H := F.toGES) Sum.getRight?
    (fun {s} h => (pmapSet_inr s) ▸ sum_con_R (c := s) h) (fun {X u x} hX hu => ?_) hc
  cases u with
  | inr z =>
    obtain ⟨Y, hY, hen⟩ := hX
    exact ⟨Y, fun y hy => ⟨Sum.inr y, hY y hy, rfl⟩, (by simpa using hu : z = x) ▸ hen⟩
  | inl z => exact absurd hu (by simp)
end CCS
