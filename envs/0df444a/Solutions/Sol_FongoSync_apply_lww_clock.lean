-- Prove2me | solution 1 for FongoSync.apply_lww_clock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:41.935794+00:00
-- url     : https://prove2.me/submissions/69f74b91-eb59-4598-8108-85fdfe14e9e3

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_apply_lww

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
theorem _root_.solution (held e : Entry V) :
    (apply .lww (some held) e).map (·.clock) =
      some (if held.clock < e.clock then e.clock else held.clock) := by
  rw [apply_lww, keep_held]
  by_cases h : held.clock < e.clock
  · have h' : compare held.clock e.clock = .lt := h
    simp [h, h']
  · have h' : compare held.clock e.clock ≠ .lt := h
    simp [h, h']
end FongoSync
