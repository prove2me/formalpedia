-- Prove2me | solution 1 for FongoSync.not_live_of_deleted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:34.305067+00:00
-- url     : https://prove2.me/submissions/dfbef67e-e2bc-4499-820c-6f4eba4d742c

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View

set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false
namespace FongoSync
theorem _root_.solution (sc : Schema) (inp : Inputs) (g : Gid)
    (hd : deleted sc inp g) : ¬ Live sc inp g := by
  rintro ⟨k, hk⟩
  induction k with
  | zero => exact hk
  | succ k ih =>
    rcases hk with hk | ⟨_, hnd, _⟩
    · exact ih hk
    · exact hnd hd
end FongoSync
