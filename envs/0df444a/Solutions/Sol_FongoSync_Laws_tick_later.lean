-- Prove2me | solution 1 for FongoSync.Laws.tick_later
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:49.896437+00:00
-- url     : https://prove2.me/submissions/12277df6-3040-4f41-85e6-aff742847f67

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_Clock_tick_lt


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (c : Clock) (wall : Nat) : c.last < (c.tick wall).1 :=
  c.tick_lt wall
end FongoSync.Laws
