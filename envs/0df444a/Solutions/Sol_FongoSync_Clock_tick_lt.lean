-- Prove2me | solution 1 for FongoSync.Clock.tick_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:01:55.261921+00:00
-- url     : https://prove2.me/submissions/406bbb86-c410-4e56-a509-0913d87fe90e


import Definitions.Def_FongoSync_Clock
import Theorems.Thm_FongoSync_Hlc_lt_of_before
import Theorems.Thm_FongoSync_Clock_tick_before

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace Clock
theorem _root_.solution (c : Clock) (wall : Nat) : c.last < (c.tick wall).1 :=
  Hlc.lt_of_before (c.tick_before wall)
end Clock
end FongoSync
