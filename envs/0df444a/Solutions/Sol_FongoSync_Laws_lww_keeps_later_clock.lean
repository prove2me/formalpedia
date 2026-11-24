-- Prove2me | solution 1 for FongoSync.Laws.lww_keeps_later_clock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:14.394956+00:00
-- url     : https://prove2.me/submissions/1d53d4e9-c592-47c2-ba1d-7889aa682ba7

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_apply_lww_clock


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]
namespace FongoSync.Laws
theorem _root_.solution (held e : Entry V) :
    (apply .lww (some held) e).map (·.clock) =
      some (if held.clock < e.clock then e.clock else held.clock) :=
  apply_lww_clock held e
end FongoSync.Laws
