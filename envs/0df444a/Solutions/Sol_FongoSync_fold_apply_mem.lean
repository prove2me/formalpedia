-- Prove2me | solution 1 for FongoSync.fold_apply_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:07.12156+00:00
-- url     : https://prove2.me/submissions/bc7135fb-b56f-47d1-8537-1c4b6ffa5587

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_fold_keep_spec
import Theorems.Thm_FongoSync_apply_lww
import Theorems.Thm_FongoSync_apply_max

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
theorem _root_.solution (s : Strategy) (l : List (Entry V)) (m : Entry V)
    (h : l.foldl (apply s) none = some m) : m ∈ l := by
  cases s
  · rw [show apply (V := V) .lww = keep compare Entry.clock from funext fun h => funext fun e => apply_lww h e] at h
    simpa using (fold_keep_spec l none m h).1
  · rw [show apply (V := V) .max = keep maxCmp Entry.pair from funext fun h => funext fun e => apply_max h e] at h
    simpa using (fold_keep_spec l none m h).1
end FongoSync
