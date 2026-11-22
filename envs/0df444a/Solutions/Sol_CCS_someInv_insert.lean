-- Prove2me | solution 1 for CCS.someInv_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:57:21.794814+00:00
-- url     : https://prove2.me/submissions/05bed944-bc2b-450d-8687-3276a9d8c633

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
theorem _root_.solution {c : Set (Option E.Event)} {x : E.Event} :
    {z | some z ∈ c ∪ ({some x} : Set (Option E.Event))} = {z | some z ∈ c} ∪ {x} := by
  ext z
  constructor
  · rintro (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (Option.some.inj (Set.mem_singleton_iff.mp hz))
  · rintro (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (by rw [Set.mem_singleton_iff.mp hz]; rfl)
end CCS
