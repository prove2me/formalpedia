-- Prove2me | solution 1 for FongoSync.Laws.tick_after_observe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:52.981423+00:00
-- url     : https://prove2.me/submissions/1fec5287-658b-4429-9e0a-e7c165aa9e9a

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_Clock_observe_then_tick


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (c : Clock) (remote : Hlc) (wall : Nat) (h : remote.encodable) :
    remote < ((c.observe remote).tick wall).1 :=
  c.observe_then_tick remote wall h
end FongoSync.Laws
