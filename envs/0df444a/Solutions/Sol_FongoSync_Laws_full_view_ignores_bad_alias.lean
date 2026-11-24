-- Prove2me | solution 1 for FongoSync.Laws.full_view_ignores_bad_alias
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:09:29.362285+00:00
-- url     : https://prove2.me/submissions/a2326117-e758-4458-9497-a54e52af8367

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_Full_view_ignores_bad_alias


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (sc : Full.Schema) (c : Change Value)
    (cs : List (Change Value)) (h : aliasOk c = false) :
    Full.view sc (c :: cs) = Full.view sc cs :=
  Full.view_ignores_bad_alias sc c cs h
end FongoSync.Laws
