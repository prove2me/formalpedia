-- Prove2me | solution 1 for CCS.inlInv_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:57:27.388645+00:00
-- url     : https://prove2.me/submissions/bf83d63a-c452-4eb0-beb4-0d5a6debbde3

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
theorem _root_.solution {c : Set (E.Event ⊕ F.Event)} {x : E.Event} :
    {z | Sum.inl z ∈ c ∪ ({Sum.inl x} : Set (E.Event ⊕ F.Event))} = {z | Sum.inl z ∈ c} ∪ {x} := by
  ext z
  constructor
  · rintro (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (by simpa using Set.mem_singleton_iff.mp hz)
  · rintro (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (by rw [Set.mem_singleton_iff.mp hz]; rfl)
end CCS
