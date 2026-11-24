-- Prove2me | solution 1 for FongoSync.Laws.max_any_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:18.030814+00:00
-- url     : https://prove2.me/submissions/9ec83a5a-3c40-485d-baf1-f5f0b1d38307

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_Entry_pair_inj
import Theorems.Thm_FongoSync_apply_max
import Theorems.Thm_FongoSync_keep_swap


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]
namespace FongoSync.Laws
theorem _root_.solution (h : Option (Entry V)) (a b : Entry V) :
    apply .max (apply .max h a) b = apply .max (apply .max h b) a := by
  simp only [apply_max]; exact keep_swap h a b Entry.pair_inj
end FongoSync.Laws
