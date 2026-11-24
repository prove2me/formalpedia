-- Prove2me | solution 1 for FongoSync.Full.view_ignores_unknown_collection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:10.396956+00:00
-- url     : https://prove2.me/submissions/756de955-70b1-4be6-b187-0b0ee7058672

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_view_ignores

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
namespace FongoSync.Full
theorem _root_.solution (sc : Schema) (c : Change Value) (cs : List (Change Value))
    (h : sc.find c.collection = none) : view sc (c :: cs) = view sc cs :=
  view_ignores sc c cs fun h' => by simp [h] at h'
end FongoSync.Full
