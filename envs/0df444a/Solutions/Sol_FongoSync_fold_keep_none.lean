-- Prove2me | solution 1 for FongoSync.fold_keep_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:29.98068+00:00
-- url     : https://prove2.me/submissions/f6000bce-3013-44bd-b689-1bcc900ad39e

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_keep_some

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {E K : Type} (cmp : K → K → Ordering) (key : E → K)
variable [TransCmp cmp] [LawfulEqCmp cmp]
variable {cmp key}
namespace FongoSync
theorem _root_.solution (l : List E) (h : Option E) :
    l.foldl (keep cmp key) h = none ↔ h = none ∧ l = [] := by
  induction l generalizing h with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl, ih, reduceCtorEq, and_false, iff_false, not_and]
    intro hk
    have ⟨m, hm⟩ := keep_some (cmp := cmp) (key := key) h x
    rw [hm] at hk; cases hk
end FongoSync
