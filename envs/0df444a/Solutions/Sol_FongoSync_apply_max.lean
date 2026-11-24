-- Prove2me | solution 1 for FongoSync.apply_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:03.672092+00:00
-- url     : https://prove2.me/submissions/ced2d325-4130-45c8-aa61-2f0479a394f5

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_wins_max

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
theorem _root_.solution (held : Option (Entry V)) (e : Entry V) :
    apply .max held e = keep maxCmp Entry.pair held e := by
  cases held with
  | none => rfl
  | some s =>
    simp only [apply, wins_max, keep_held, maxCmp, Entry.pair, compareLex, compareOn]
    by_cases h : (compare s.value e.value).then (compare s.clock e.clock) = .lt <;> simp [h]
end FongoSync
