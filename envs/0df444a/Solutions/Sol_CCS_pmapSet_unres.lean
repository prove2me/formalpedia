-- Prove2me | solution 1 for CCS.pmapSet_unres
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:57:18.043992+00:00
-- url     : https://prove2.me/submissions/293d6196-5022-4849-98ca-b26be2a1265f

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Definitions.Def_EventStructures_CCS_Semantics
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



set_option autoImplicit true
open PES Configuration ConfFamily
open CCS
variable {Name : Type*}
variable {Name : Type*}
variable {E F : SES (Action Name)} {α : Action Name}
namespace CCS
theorem _root_.solution {E : SES (Action (Option Name))} (s : Set (restrict E).Event) :
    GES.pmapSet (G := (restrict E).toGES) (H := E.toGES) (fun e => some e.1) s
      = {y | ∃ hy, (⟨y, hy⟩ : (restrict E).Event) ∈ s} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨u, hu, hev⟩
    have hy : u.1 = y := by simpa using hev
    subst hy
    exact ⟨u.2, hu⟩
  · rintro y ⟨hy, hm⟩
    exact ⟨⟨y, hy⟩, hm, rfl⟩
end CCS
