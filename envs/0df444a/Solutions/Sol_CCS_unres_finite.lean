-- Prove2me | solution 1 for CCS.unres_finite
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T21:16:43.089882+00:00
-- url     : https://prove2.me/submissions/f63243dc-9545-40b7-a3cf-b79bdd708c41

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

theorem CCS.unres_finite (h : c.Finite) : (unres c).Finite := by
  have e : unres c = Subtype.val '' c := by
    ext y
    constructor
    · rintro ⟨h, hm⟩
      exact ⟨_, hm, rfl⟩
    · rintro ⟨⟨y', h⟩, hm, rfl⟩
      exact ⟨h, hm⟩
  rw [e]
  exact h.image _

theorem solution (h : c.Finite) : (unres c).Finite := CCS.unres_finite h
