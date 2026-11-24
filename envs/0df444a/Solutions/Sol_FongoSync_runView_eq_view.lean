-- Prove2me | solution 1 for FongoSync.runView_eq_view
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:39.033648+00:00
-- url     : https://prove2.me/submissions/6c53a046-32ba-40c5-894d-e8e349b373d7

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
import Theorems.Thm_FongoSync_presentR_eq

set_option autoImplicit false
open FongoSync
open Classical
namespace FongoSync
theorem _root_.solution (sc : Schema) (cs : List (Change Value)) : runView sc cs = view sc cs :=
  presentR_eq sc (inputs sc cs)
end FongoSync
