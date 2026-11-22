-- Prove2me | solution 1 for CCS.mem_unres
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:57:59.783878+00:00
-- url     : https://prove2.me/submissions/0d7e1c7b-da38-421f-b3e2-c1bda8b35959

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
variable {E : SES (Action (Option Name))} {c : Set (restrict E).Event}
namespace CCS
theorem _root_.solution {x : E.Event} (hx : (E.label x).strip.isSome = true) :
    x ∈ unres c ↔ (⟨x, hx⟩ : (restrict E).Event) ∈ c := by
  constructor
  · rintro ⟨h, hm⟩; exact hm
  · intro h; exact ⟨hx, h⟩
end CCS
