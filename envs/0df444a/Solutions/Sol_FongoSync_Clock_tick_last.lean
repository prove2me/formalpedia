-- Prove2me | solution 1 for FongoSync.Clock.tick_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:00.560048+00:00
-- url     : https://prove2.me/submissions/c71bfa30-d050-49aa-b6d4-264a1ff48073


import Definitions.Def_FongoSync_Clock

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace Clock
theorem _root_.solution (c : Clock) (wall : Nat) : (c.tick wall).2.last = (c.tick wall).1 := rfl
end Clock
end FongoSync
