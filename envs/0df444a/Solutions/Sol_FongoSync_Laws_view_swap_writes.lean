-- Prove2me | solution 1 for FongoSync.Laws.view_swap_writes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:09:02.596414+00:00
-- url     : https://prove2.me/submissions/8a4dc61a-1a95-4a98-8a6b-3cf7d9b1e649

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_view_swap


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (sc : Schema) (pre post : List (Change Value)) (a b : Change Value)
    (h : Compatible a b) :
    view sc (pre ++ a :: b :: post) = view sc (pre ++ b :: a :: post) :=
  view_swap sc pre post a b (.inr (.inr h))
end FongoSync.Laws
