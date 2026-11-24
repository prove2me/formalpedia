-- Prove2me | solution 1 for FongoSync.liveAt_succ_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:01:16.661885+00:00
-- url     : https://prove2.me/submissions/11852611-1ec9-4594-85f8-468dc130d5f9

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution {k : Nat} {g : Gid} (h : liveAt sc inp k g) : liveAt sc inp (k + 1) g :=
  .inl h
end FongoSync
