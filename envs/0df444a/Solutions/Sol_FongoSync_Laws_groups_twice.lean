-- Prove2me | solution 1 for FongoSync.Laws.groups_twice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:56.927772+00:00
-- url     : https://prove2.me/submissions/daacea9e-ac51-4b1d-a7fe-a426101a6309

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_canonical_eq_of_mem_iff


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (pre post : List Edge) (x : Edge) :
    canonical (pre ++ x :: x :: post) = canonical (pre ++ x :: post) :=
  canonical_eq_of_mem_iff _ _ fun e => by simp
end FongoSync.Laws
