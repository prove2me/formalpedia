-- Prove2me | solution 1 for FongoSync.Laws.view_twice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:09:06.446022+00:00
-- url     : https://prove2.me/submissions/3264cd3d-6032-4387-ab1d-0cd6c7c13066

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_view_twice


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (sc : Schema) (pre post : List (Change Value)) (a : Change Value) :
    view sc (pre ++ a :: a :: post) = view sc (pre ++ a :: post) :=
  FongoSync.view_twice sc pre post a
end FongoSync.Laws
