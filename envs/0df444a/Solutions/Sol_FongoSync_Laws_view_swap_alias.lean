-- Prove2me | solution 1 for FongoSync.Laws.view_swap_alias
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:09:05.684419+00:00
-- url     : https://prove2.me/submissions/1803e55c-866e-4f5c-9e20-832d765d5dbe

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
    (h : a.field = ALIAS) :
    view sc (pre ++ a :: b :: post) = view sc (pre ++ b :: a :: post) :=
  view_swap sc pre post a b (.inl h)
end FongoSync.Laws
