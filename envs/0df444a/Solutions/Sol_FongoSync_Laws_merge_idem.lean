-- Prove2me | solution 1 for FongoSync.Laws.merge_idem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:59.283387+00:00
-- url     : https://prove2.me/submissions/83470f19-425f-4e17-b438-4faba8aa6bca

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_merge_idem


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]
namespace FongoSync.Laws
theorem _root_.solution (s : Strategy) (a : Option (Entry V)) : merge s a a = a :=
  FongoSync.merge_idem s a
end FongoSync.Laws
