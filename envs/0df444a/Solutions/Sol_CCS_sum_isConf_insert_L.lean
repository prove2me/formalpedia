-- Prove2me | solution 1 for CCS.sum_isConf_insert_L
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:24.983123+00:00
-- url     : https://prove2.me/submissions/4b4f5411-d08f-49b8-83dd-fe3e11903005

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Definitions.Def_EventStructures_CCS_Semantics
import Theorems.Thm_CCS_pmapSet_inl
import Theorems.Thm_CCS_sum_isConf_R
import Theorems.Thm_CCS_Action_strip_map
import Theorems.Thm_CCS_Label_co_co
import Theorems.Thm_CCS_Label_strip_map
import Theorems.Thm_GES_isConf_insert_pmap
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
theorem _root_.solution {c : Set (E.Event ⊕ F.Event)} {x : E.Event}
    (hc : (sum E F).toGES.isConf c) (hnoR : ¬ ∃ f, Sum.inr f ∈ c)
    (hx : E.toGES.isConf ({z | Sum.inl z ∈ c} ∪ {x})) :
    (sum E F).toGES.isConf (c ∪ {Sum.inl x}) := by
  classical
  refine GES.isConf_insert_pmap (G := (sum E F).toGES) (H := E.toGES) Sum.getLeft? hc rfl
    ?_ ?_ ((pmapSet_inl c) ▸ hx)
  · refine fun W hW => ⟨fun e he f hf => ?_, fun V hV => ?_, fun V hV => ?_⟩
    · rcases hW (by exact_mod_cast hf) with h | h
      · exact hnoR ⟨f, h⟩
      · exact absurd (Set.mem_singleton_iff.mp h) (by simp)
    · refine hx.1 V fun z hz => ?_
      rcases hW (hV hz) with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa using Set.mem_singleton_iff.mp h)
    · refine (sum_isConf_R hc).1 V fun z hz => ?_
      rcases hW (hV hz) with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) (by simp)
  · intro Y hY hen
    refine ⟨Y.image Sum.inl, ?_, Y, ?_, hen⟩
    · intro u hu
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
      obtain ⟨v, hv, hev⟩ := hY y hy
      cases v with
      | inl w => exact (by simpa using hev : w = y) ▸ hv
      | inr w => exact absurd hev (by simp)
    · intro y hy
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
end CCS
