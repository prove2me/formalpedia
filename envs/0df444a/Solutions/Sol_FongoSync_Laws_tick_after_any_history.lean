-- Prove2me | solution 1 for FongoSync.Laws.tick_after_any_history
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:55.599182+00:00
-- url     : https://prove2.me/submissions/bc76eaaf-e839-498e-8c97-98b80faadecf

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_Clock_tick_after_any_history


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (c : Clock) (events : List Event) (wall : Nat) :
    c.last < ((c.run events).1.tick wall).1 ∧
      ∀ r ∈ (c.run events).2, r < ((c.run events).1.tick wall).1 :=
  c.tick_after_any_history events wall
end FongoSync.Laws
