-- Prove2me | solution 1 for FongoSync.apply_any_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:29.682732+00:00
-- url     : https://prove2.me/submissions/5e4e62a1-a0e4-418c-99d1-07356b0552cc

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_keep_swap
import Theorems.Thm_FongoSync_apply_lww
import Theorems.Thm_FongoSync_apply_max
import Theorems.Thm_FongoSync_Entry_pair_inj

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
theorem _root_.solution (s : Strategy) (h : Option (Entry V)) (a b : Entry V)
    (unique : a.clock = b.clock → a = b) :
    apply s (apply s h a) b = apply s (apply s h b) a := by
  cases s
  · simp only [apply_lww]; exact keep_swap h a b unique
  · simp only [apply_max]; exact keep_swap h a b Entry.pair_inj
end FongoSync
