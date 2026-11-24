-- Prove2me | solution 1 for FongoSync.liveCount_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:47.767383+00:00
-- url     : https://prove2.me/submissions/ef442e0a-99bb-46f3-b89c-27f3b07d16f4

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution (k : Nat) : liveCount sc inp k ≤ inp.gids.length :=
  List.length_filter_le _ _
end FongoSync
