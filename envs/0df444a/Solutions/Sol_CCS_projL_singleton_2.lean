-- Prove2me | solution 2 for CCS.projL_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:22:20.588797+00:00
-- url     : https://prove2.me/submissions/2f41096a-e6b8-4ffd-8195-0ad579e5f108

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par

set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}
namespace CCS
theorem _root_.solution (t : Tag E F) : projL {t} = {e | t.evL = some e} := by
  ext e
  constructor
  · rintro ⟨t', ht', he⟩; rw [Set.mem_singleton_iff] at ht'; exact ht' ▸ he
  · intro he; exact ⟨t, rfl, he⟩
end CCS
