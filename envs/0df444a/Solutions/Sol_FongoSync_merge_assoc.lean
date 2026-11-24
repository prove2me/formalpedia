-- Prove2me | solution 1 for FongoSync.merge_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:03.859009+00:00
-- url     : https://prove2.me/submissions/586ac1b5-cc37-423e-aed7-69b8c2ed200b

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_join_assoc
import Theorems.Thm_FongoSync_merge_eq_join

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
theorem _root_.solution (s : Strategy) (a b c : Option (Entry V)) :
    merge s (merge s a b) c = merge s a (merge s b c) := by
  simp only [merge_eq_join]
  cases s
  · exact join_assoc a b c
  · exact join_assoc a b c
end FongoSync
