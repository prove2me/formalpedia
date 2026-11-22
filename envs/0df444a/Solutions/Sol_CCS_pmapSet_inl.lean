-- Prove2me | solution 1 for CCS.pmapSet_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:56:43.412808+00:00
-- url     : https://prove2.me/submissions/53771e2b-4732-48a2-b1a8-7ecc28b7426f

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
theorem _root_.solution (s : Set (E.Event ⊕ F.Event)) :
    GES.pmapSet (G := (sum E F).toGES) (H := E.toGES) Sum.getLeft? s
      = {z | Sum.inl z ∈ s} := by
  refine Set.Subset.antisymm ?_ fun z hz => ⟨Sum.inl z, hz, rfl⟩
  rintro z ⟨u, hu, hev⟩
  cases u with
  | inl w => exact (by simpa using hev : w = z) ▸ hu
  | inr w => exact absurd hev (by simp)
end CCS
