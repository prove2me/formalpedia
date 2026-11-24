-- Prove2me | solution 1 for FongoSync.fold_keep_dup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:06.491074+00:00
-- url     : https://prove2.me/submissions/4651c1b0-d266-4ca3-9ef3-cacd412af9e3

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_fold_keep_eq_of_mem_iff

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {E K : Type} (cmp : K → K → Ordering) (key : E → K)
variable [TransCmp cmp] [LawfulEqCmp cmp]
variable {cmp key}
namespace FongoSync
theorem _root_.solution (l : List E) (inj : KeyInj key l) :
    (l ++ l).foldl (keep cmp key) none = l.foldl (keep cmp key) none :=
  fold_keep_eq_of_mem_iff _ _ (by simp) (by intro a ha b hb; simp at ha hb; exact inj a ha b hb)
end FongoSync
