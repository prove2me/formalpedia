-- Prove2me | solution 1 for CCS.projL_eq_pmap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:23:05.14495+00:00
-- url     : https://prove2.me/submissions/9c23eeff-948d-45c3-96cd-9fa706b7a2b0

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par

set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}
variable {c : Set (Tag E F)}
namespace CCS
theorem _root_.solution (c : Set (Tag E F)) :
    projL c = GES.pmapSet (G := (parSES E F).toGES) (H := E.toGES) Tag.evL c := rfl
end CCS
