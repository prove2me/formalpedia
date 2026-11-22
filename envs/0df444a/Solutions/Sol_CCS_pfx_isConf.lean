-- Prove2me | solution 1 for CCS.pfx_isConf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:21.155602+00:00
-- url     : https://prove2.me/submissions/825193c1-b0a4-4426-8d59-59e71142436b

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Definitions.Def_EventStructures_CCS_Semantics
import Theorems.Thm_CCS_pmapSet_pfx
import Theorems.Thm_CCS_pfx_con
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
theorem _root_.solution {c : Set (Option E.Event)}
    (hc : (pfx α E).toGES.isConf c) : E.toGES.isConf {z | some z ∈ c} := by
  refine (pmapSet_pfx (α := α) c) ▸ GES.isConf_pmap (G := (pfx α E).toGES) (H := E.toGES) id
    (fun {s} h => (pmapSet_pfx (α := α) s) ▸ pfx_con (c := s) h)
    (fun {X u x} hX hu => ?_) hc
  cases u with
  | none => exact absurd hu (by simp)
  | some z =>
    obtain ⟨-, Y, hY, hen⟩ := hX
    exact ⟨Y, fun y hy => ⟨some y, hY y hy, rfl⟩, (Option.some.inj hu) ▸ hen⟩
end CCS
