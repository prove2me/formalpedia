-- Prove2me | solution 1 for CCS.sum_not_mixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:57:06.448107+00:00
-- url     : https://prove2.me/submissions/da0b2b8f-6eea-4e57-a4f1-bed309404f0b

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Definitions.Def_EventStructures_CCS_Semantics

set_option autoImplicit true
open PES Configuration ConfFamily
open CCS
variable {Name : Type*}
variable {Name : Type*}
variable {E F : SES (Action Name)} {α : Action Name}
namespace CCS
theorem _root_.solution {c : Set (E.Event ⊕ F.Event)} (hc : (sum E F).toGES.isConf c)
    {z : E.Event} (hz : Sum.inl z ∈ c) {w : F.Event} (hw : Sum.inr w ∈ c) : False := by
  classical
  exact (hc.1 {Sum.inl z, Sum.inr w} (by
    intro u hu
    rcases Finset.mem_insert.mp (by exact_mod_cast hu) with rfl | hu'
    · exact hz
    · exact (Finset.mem_singleton.mp hu') ▸ hw)).1 z (Finset.mem_insert_self _ _) w
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
end CCS
