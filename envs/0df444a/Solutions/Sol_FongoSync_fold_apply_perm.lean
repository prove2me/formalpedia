-- Prove2me | solution 1 for FongoSync.fold_apply_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:09.767409+00:00
-- url     : https://prove2.me/submissions/c26adaed-f1de-48cd-af75-b4710617a916

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_apply_any_order

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
theorem _root_.solution (s : Strategy) {l₁ l₂ : List (Entry V)} (p : l₁.Perm l₂)
    (unique : UniqueClocks l₁) (h : Option (Entry V)) :
    l₁.foldl (apply s) h = l₂.foldl (apply s) h :=
  p.foldl_eq' (fun x hx y hy z => apply_any_order s z x y (unique x hx y hy)) h
end FongoSync
