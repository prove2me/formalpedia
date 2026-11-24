-- Prove2me | solution 1 for FongoSync.Laws.apply_twice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:14.899868+00:00
-- url     : https://prove2.me/submissions/8af403fd-762b-4772-92c2-cdc6c713b9cd

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_State_apply_twice
import Theorems.Thm_FongoSync_apply_twice


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]
namespace FongoSync.Laws
theorem _root_.solution (s : Strategy) (h : Option (Entry V)) (e : Entry V) :
    apply s (apply s h e) e = apply s h e :=
  FongoSync.apply_twice s h e
end FongoSync.Laws
