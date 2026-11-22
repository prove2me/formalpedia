-- Prove2me | solution 1 for CCS.projR_eq_pmap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:23:11.411127+00:00
-- url     : https://prove2.me/submissions/f6776e38-5004-4748-94bc-eba51a1e10df

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
    projR c = GES.pmapSet (G := (parSES E F).toGES) (H := F.toGES) Tag.evR c := rfl
end CCS
