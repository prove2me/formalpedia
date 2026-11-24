-- Prove2me | solution 1 for FongoSync.fold_apply_dup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:10.30035+00:00
-- url     : https://prove2.me/submissions/85eafccd-a2e4-4f6e-b818-2b12541e3dbe

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_fold_apply_eq_of_mem_iff

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
theorem _root_.solution (s : Strategy) (l : List (Entry V)) (unique : UniqueClocks l) :
    (l ++ l).foldl (apply s) none = l.foldl (apply s) none :=
  fold_apply_eq_of_mem_iff s _ _ (by simp) (by intro a ha b hb; simp at ha hb; exact unique a ha b hb)
end FongoSync
