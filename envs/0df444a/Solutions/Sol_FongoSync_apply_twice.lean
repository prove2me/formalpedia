-- Prove2me | solution 1 for FongoSync.apply_twice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:28.05361+00:00
-- url     : https://prove2.me/submissions/0d71db83-cda1-45ec-a9a8-4b03334728f3

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_keep_idem
import Theorems.Thm_FongoSync_apply_lww
import Theorems.Thm_FongoSync_apply_max

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
theorem _root_.solution (s : Strategy) (h : Option (Entry V)) (e : Entry V) :
    apply s (apply s h e) e = apply s h e := by
  cases s
  · simp only [apply_lww]; exact keep_idem h e
  · simp only [apply_max]; exact keep_idem h e
end FongoSync
