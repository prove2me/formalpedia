-- Prove2me | solution 1 for FongoSync.Laws.apply_any_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:17.478202+00:00
-- url     : https://prove2.me/submissions/4151f3fd-63d0-47bd-9f41-094532e653f1

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_apply_any_order


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]
namespace FongoSync.Laws
theorem _root_.solution (s : Strategy) (h : Option (Entry V)) (a b : Entry V)
    (unique : a.clock = b.clock → a = b) :
    apply s (apply s h a) b = apply s (apply s h b) a :=
  FongoSync.apply_any_order s h a b unique
end FongoSync.Laws
