-- Prove2me | solution 1 for FongoSync.Laws.merge_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:58.880703+00:00
-- url     : https://prove2.me/submissions/6a1b7b22-528f-4824-9856-c9cbdadc008e

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_merge_assoc


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]
namespace FongoSync.Laws
theorem _root_.solution (s : Strategy) (a b c : Option (Entry V)) :
    merge s (merge s a b) c = merge s a (merge s b c) :=
  FongoSync.merge_assoc s a b c
end FongoSync.Laws
