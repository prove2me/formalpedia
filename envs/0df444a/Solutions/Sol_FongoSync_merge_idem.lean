-- Prove2me | solution 1 for FongoSync.merge_idem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:56.902132+00:00
-- url     : https://prove2.me/submissions/430f726e-ad04-4bc8-adda-58ff08e3e4b6

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_join_idem
import Theorems.Thm_FongoSync_merge_eq_join

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
theorem _root_.solution (s : Strategy) (a : Option (Entry V)) : merge s a a = a := by
  rw [merge_eq_join]; cases s <;> exact join_idem a
end FongoSync
