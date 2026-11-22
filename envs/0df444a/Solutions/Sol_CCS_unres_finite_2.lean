-- Prove2me | solution 2 for CCS.unres_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:23:15.861663+00:00
-- url     : https://prove2.me/submissions/78040b54-22e3-40b2-9700-c76524c3d564

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Definitions.Def_EventStructures_CCS_Semantics
import Theorems.Thm_CCS_unres_eq_image

set_option autoImplicit true
open PES Configuration ConfFamily
open CCS
variable {Name : Type*}
variable {Name : Type*}
variable {E F : SES (Action Name)} {α : Action Name}
variable {E : SES (Action (Option Name))} {c : Set (restrict E).Event}
namespace CCS
theorem _root_.solution (h : c.Finite) : (unres c).Finite := by
  rw [unres_eq_image]; exact h.image _
end CCS
