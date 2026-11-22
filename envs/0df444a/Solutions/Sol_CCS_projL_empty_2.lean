-- Prove2me | solution 2 for CCS.projL_empty
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T21:21:44.905808+00:00
-- url     : https://prove2.me/submissions/e0fe7a0d-1e44-4da6-bb9a-bd04b029b711

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}

theorem CCS.projL_empty : projL (∅ : Set (Tag E F)) = ∅ := by
  ext f
  simp [projL]

theorem solution : projL (∅ : Set (Tag E F)) = ∅ := CCS.projL_empty
