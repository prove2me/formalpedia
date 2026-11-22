-- Prove2me | solution 1 for CCS.resid_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:54:21.033851+00:00
-- url     : https://prove2.me/submissions/323c78e1-7965-4ded-a82b-53a5cf7640cb

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation

set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}
namespace CCS
theorem _root_.solution (c : Set (semantics (.nil : Process Name)).Event) :
    resid .nil c = .nil := rfl
end CCS
