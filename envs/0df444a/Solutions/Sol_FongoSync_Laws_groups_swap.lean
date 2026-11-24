-- Prove2me | solution 1 for FongoSync.Laws.groups_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:56.273973+00:00
-- url     : https://prove2.me/submissions/dc5437fa-2a21-4566-b974-76a5e458e481

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_canonical_perm


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (pre post : List Edge) (x y : Edge) :
    canonical (pre ++ x :: y :: post) = canonical (pre ++ y :: x :: post) :=
  canonical_perm (List.Perm.append_left pre (List.Perm.swap y x post))
end FongoSync.Laws
