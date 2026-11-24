-- Prove2me | solution 1 for FongoSync.Clock.observe_then_tick
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:04.367878+00:00
-- url     : https://prove2.me/submissions/394905ec-f87c-4ae4-9869-45470a1c3259


import Definitions.Def_FongoSync_Clock
import Theorems.Thm_FongoSync_Hlc_lt_of_before
import Theorems.Thm_FongoSync_Hlc_before_of_notAfter_of_before
import Theorems.Thm_FongoSync_Clock_tick_before
import Theorems.Thm_FongoSync_Clock_observe_notAfter

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace Clock
theorem _root_.solution (c : Clock) (remote : Hlc) (wall : Nat)
    (h : remote.encodable) : remote < ((c.observe remote).tick wall).1 :=
  Hlc.lt_of_before <| Hlc.before_of_notAfter_of_before
    ((c.observe_notAfter remote).2 h) ((c.observe remote).tick_before wall)
end Clock
end FongoSync
