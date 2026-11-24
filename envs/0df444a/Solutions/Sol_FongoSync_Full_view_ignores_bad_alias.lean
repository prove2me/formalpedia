-- Prove2me | solution 1 for FongoSync.Full.view_ignores_bad_alias
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:23.199086+00:00
-- url     : https://prove2.me/submissions/9a52a0cd-b0a6-4534-8f79-9d958f563b6d

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_view_ignores

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
namespace FongoSync.Full
theorem _root_.solution (sc : Schema) (c : Change Value) (cs : List (Change Value))
    (h : aliasOk c = false) : view sc (c :: cs) = view sc cs :=
  view_ignores sc c cs fun h' => by simp [h] at h'
end FongoSync.Full
