-- Prove2me | solution 1 for FongoSync.merge_eq_join
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:31.477372+00:00
-- url     : https://prove2.me/submissions/b5a0ff19-a245-4a02-81f6-9d3820908c5f

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_apply_lww
import Theorems.Thm_FongoSync_apply_max

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
theorem _root_.solution (s : Strategy) (a b : Option (Entry V)) :
    merge s a b = match s with
      | .lww => join compare Entry.clock a b
      | .max => join maxCmp Entry.pair a b := by
  cases s <;> cases b <;> simp [merge, join, apply_lww, apply_max]
end FongoSync
