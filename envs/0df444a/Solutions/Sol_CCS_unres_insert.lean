-- Prove2me | solution 1 for CCS.unres_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:58:15.079994+00:00
-- url     : https://prove2.me/submissions/2cc219b2-601d-4101-9aa7-238a48ed540c

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
    unres (c ∪ {⟨x, hx⟩}) = unres c ∪ {x} := by
  ext y
  constructor
  · rintro ⟨h, hm | hm⟩
    · exact Or.inl ⟨h, hm⟩
    · exact Or.inr (congrArg Subtype.val hm)
  · rintro (⟨h, hm⟩ | hm)
    · exact ⟨h, Or.inl hm⟩
    · exact ⟨hm ▸ hx, Or.inr (Subtype.ext hm)⟩
end CCS
