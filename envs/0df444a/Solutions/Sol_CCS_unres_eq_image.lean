-- Prove2me | solution 1 for CCS.unres_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:10:58.700023+00:00
-- url     : https://prove2.me/submissions/fa035080-bd59-4dc2-b87a-9dcc8803406c

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
theorem _root_.solution : unres c = Subtype.val '' c := by
  ext y
  constructor
  · rintro ⟨h, hm⟩; exact ⟨⟨y, h⟩, hm, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z.2, hz⟩
end CCS
