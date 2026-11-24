-- Prove2me | solution 1 for FongoSync.Laws.full_view_ignores_unencodable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:09:26.040323+00:00
-- url     : https://prove2.me/submissions/9502d591-5cf4-46b0-ab23-b1cf56af913d

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_Full_view_ignores_unencodable


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (sc : Full.Schema) (c : Change Value)
    (cs : List (Change Value)) (h : ¬ c.clock.encodable) :
    Full.view sc (c :: cs) = Full.view sc cs :=
  Full.view_ignores_unencodable sc c cs h
end FongoSync.Laws
