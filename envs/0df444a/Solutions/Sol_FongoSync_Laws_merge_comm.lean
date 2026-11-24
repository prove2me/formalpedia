-- Prove2me | solution 1 for FongoSync.Laws.merge_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:56.069722+00:00
-- url     : https://prove2.me/submissions/63190d5c-7649-4891-a633-bba611a78eb4

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_merge_comm


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]
namespace FongoSync.Laws
theorem _root_.solution (s : Strategy) (a b : Option (Entry V))
    (unique : ∀ x ∈ a, ∀ y ∈ b, x.clock = y.clock → x = y) :
    merge s a b = merge s b a :=
  FongoSync.merge_comm s a b unique
end FongoSync.Laws
