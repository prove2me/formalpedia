-- Prove2me | solution 1 for CCS.projL_singleton
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T21:19:51.763633+00:00
-- url     : https://prove2.me/submissions/7796abfb-60b6-4165-a08a-6dd904d0db27

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}

theorem CCS.projL_singleton (t : Tag E F) : projL {t} = {e | t.evL = some e} := by
  ext f
  simp [projL]

theorem solution (t : Tag E F) : projL {t} = {e | t.evL = some e} := CCS.projL_singleton t
