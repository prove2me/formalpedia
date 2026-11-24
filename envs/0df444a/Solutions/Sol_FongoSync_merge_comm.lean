-- Prove2me | solution 1 for FongoSync.merge_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:03.423222+00:00
-- url     : https://prove2.me/submissions/407ed535-faaf-4088-a220-c9caff26bf87

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_join_comm
import Theorems.Thm_FongoSync_Entry_pair_inj
import Theorems.Thm_FongoSync_merge_eq_join

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
theorem _root_.solution (s : Strategy) (a b : Option (Entry V))
    (unique : ∀ x ∈ a, ∀ y ∈ b, x.clock = y.clock → x = y) :
    merge s a b = merge s b a := by
  rw [merge_eq_join, merge_eq_join]
  cases s
  · exact join_comm a b unique
  · exact join_comm a b fun x _ y _ h => Entry.pair_inj h
end FongoSync
