-- Prove2me | solution 1 for FongoSync.Laws.view_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:09:16.290709+00:00
-- url     : https://prove2.me/submissions/482161a5-547a-4999-89c4-d1243f47af06

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_runView_eq_view


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (sc : Schema) (cs : List (Change Value)) : runView sc cs = view sc cs :=
  runView_eq_view sc cs
end FongoSync.Laws
