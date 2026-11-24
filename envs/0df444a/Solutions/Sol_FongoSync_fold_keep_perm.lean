-- Prove2me | solution 1 for FongoSync.fold_keep_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:02.727354+00:00
-- url     : https://prove2.me/submissions/dbbba570-00d6-4275-acff-cc57faa57074

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_keep_swap

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {E K : Type} (cmp : K → K → Ordering) (key : E → K)
variable [TransCmp cmp] [LawfulEqCmp cmp]
variable {cmp key}
namespace FongoSync
theorem _root_.solution {l₁ l₂ : List E} (p : l₁.Perm l₂) (inj : KeyInj key l₁) (h : Option E) :
    l₁.foldl (keep cmp key) h = l₂.foldl (keep cmp key) h :=
  p.foldl_eq' (fun x hx y hy z => keep_swap z x y (inj x hx y hy)) h
end FongoSync
