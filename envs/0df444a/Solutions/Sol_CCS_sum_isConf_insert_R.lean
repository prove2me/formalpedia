-- Prove2me | solution 1 for CCS.sum_isConf_insert_R
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:01.98699+00:00
-- url     : https://prove2.me/submissions/57757892-7645-4f64-9eef-3eb75f764ac9

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Definitions.Def_EventStructures_CCS_Semantics
import Theorems.Thm_CCS_pmapSet_inr
import Theorems.Thm_CCS_sum_isConf_L
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
theorem _root_.solution {c : Set (E.Event ⊕ F.Event)} {y : F.Event}
    (hc : (sum E F).toGES.isConf c) (hnoL : ¬ ∃ e, Sum.inl e ∈ c)
    (hy : F.toGES.isConf ({z | Sum.inr z ∈ c} ∪ {y})) :
    (sum E F).toGES.isConf (c ∪ {Sum.inr y}) := by
  classical
  refine GES.isConf_insert_pmap (G := (sum E F).toGES) (H := F.toGES) Sum.getRight? hc rfl
    ?_ ?_ ((pmapSet_inr c) ▸ hy)
  · refine fun W hW => ⟨fun e he f hf => ?_, fun V hV => ?_, fun V hV => ?_⟩
    · rcases hW (by exact_mod_cast he) with h | h
      · exact hnoL ⟨e, h⟩
      · exact absurd (Set.mem_singleton_iff.mp h) (by simp)
    · refine (sum_isConf_L hc).1 V fun z hz => ?_
      rcases hW (hV hz) with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) (by simp)
    · refine hy.1 V fun z hz => ?_
      rcases hW (hV hz) with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa using Set.mem_singleton_iff.mp h)
  · intro Y hY hen
    refine ⟨Y.image Sum.inr, ?_, Y, ?_, hen⟩
    · intro u hu
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
      obtain ⟨v, hv, hev⟩ := hY z hz
      cases v with
      | inr w => exact (by simpa using hev : w = z) ▸ hv
      | inl w => exact absurd hev (by simp)
    · intro z hz
      exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
end CCS
