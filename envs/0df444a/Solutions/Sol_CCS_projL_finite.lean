-- Prove2me | solution 1 for CCS.projL_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:22:23.455009+00:00
-- url     : https://prove2.me/submissions/ee51877d-f59a-49c2-a6a1-927bd0852fdd

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
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
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}
namespace CCS
theorem _root_.solution {C : Set (Tag E F)} (h : C.Finite) : (projL C).Finite := by
  have : projL C = ⋃ t ∈ C, {e | t.evL = some e} := by ext e; simp [projL]
  rw [this]
  refine h.biUnion (fun t _ => ?_)
  cases ht : t.evL with
  | none => simp
  | some x =>
    refine (Set.finite_singleton x).subset (fun e he => ?_)
    simp only [Set.mem_ofPred_eq, Option.some.injEq] at he
    simp [he]
end CCS
