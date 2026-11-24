-- Prove2me | solution 1 for FongoSync.Laws.full_view_ignores_unknown_collection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:09:27.768741+00:00
-- url     : https://prove2.me/submissions/7d3647b9-25dc-4324-948a-19726eb2f47f

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_Full_view_ignores_unknown_collection


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (sc : Full.Schema) (c : Change Value)
    (cs : List (Change Value)) (h : sc.find c.collection = none) :
    Full.view sc (c :: cs) = Full.view sc cs :=
  Full.view_ignores_unknown_collection sc c cs h
end FongoSync.Laws
