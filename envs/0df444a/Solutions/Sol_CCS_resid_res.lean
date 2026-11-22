-- Prove2me | solution 1 for CCS.resid_res
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:27.109965+00:00
-- url     : https://prove2.me/submissions/e19c416c-f0af-4b5b-99c4-f09f52500886

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation

set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}
namespace CCS
theorem _root_.solution {P : Process (Option Name)} (c : Set (semantics (.res P)).Event) :
    resid (.res P) c = .res (resid P (unres c)) := by
  rw [resid]
end CCS
