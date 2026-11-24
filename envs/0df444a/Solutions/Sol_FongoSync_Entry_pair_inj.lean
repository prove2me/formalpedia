-- Prove2me | solution 1 for FongoSync.Entry.pair_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:58:14.787892+00:00
-- url     : https://prove2.me/submissions/f513314f-a1d4-41ce-8f13-d1cc32cd8ecf

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
namespace Entry
theorem _root_.solution {a b : Entry V} (h : a.pair = b.pair) : a = b := by
  cases a; cases b; simp_all [Entry.pair]
end Entry
end FongoSync
