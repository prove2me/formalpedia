-- Prove2me | solution 2 for CCS.projR_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:22:21.091798+00:00
-- url     : https://prove2.me/submissions/d80b4d07-54a3-47a2-9cb0-79229e8842fb

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
theorem _root_.solution (t : Tag E F) : projR {t} = {f | t.evR = some f} := by
  ext f
  constructor
  · rintro ⟨t', ht', he⟩; rw [Set.mem_singleton_iff] at ht'; exact ht' ▸ he
  · intro he; exact ⟨t, rfl, he⟩
end CCS
