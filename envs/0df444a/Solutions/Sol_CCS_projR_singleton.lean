-- Prove2me | solution 1 for CCS.projR_singleton
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T21:18:10.948554+00:00
-- url     : https://prove2.me/submissions/892df999-9820-46fc-b823-56ce4d88e9df

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}

theorem CCS.projR_singleton (t : Tag E F) : projR {t} = {f | t.evR = some f} := by
  ext f
  simp [projR]

theorem solution (t : Tag E F) : projR {t} = {f | t.evR = some f} := CCS.projR_singleton t
