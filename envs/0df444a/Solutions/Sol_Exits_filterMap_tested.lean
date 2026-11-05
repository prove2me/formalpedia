-- Prove2me | solution 1 for Exits.filterMap_tested
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:46:45.627224+00:00
-- url     : https://prove2.me/submissions/49f5544d-bc1d-4c30-802d-fa1aadb9c072

import Definitions.Def_Exits_Defs
import Definitions.Def_Exits_Tested
set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Stepped

private theorem tested_nil {ν : Type} (v : ν → Bool) : tested v [] = [] := by
  simp [tested]

private theorem tested_cons_of_pass {ν : Type} {v : ν → Bool} {x : ν}
    (h : v x = true) (l : List ν) : tested v (x :: l) = [x] := by
  simp [tested, List.findIdx_cons, h]

private theorem tested_cons_of_fail {ν : Type} {v : ν → Bool} {x : ν}
    (h : v x = false) (l : List ν) : tested v (x :: l) = x :: tested v l := by
  simp [tested, List.findIdx_cons, h]

variable {α β γ τ ν : Type}
variable (sel : τ → Option ν) (v : ν → Bool) (w : τ → Bool) (hw : ∀ x, w x = ((sel x).map v).getD false)
include hw

theorem solution (xs : List τ) : (tested w xs).filterMap sel = tested v (xs.filterMap sel) := by
  induction xs with
  | nil => simp [tested_nil]
  | cons x xs ih =>
    cases h : sel x with
    | none =>
      have hx : w x = false := by rw [hw x, h]; rfl
      rw [tested_cons_of_fail hx, List.filterMap_cons_none h, List.filterMap_cons_none h, ih]
    | some y =>
      cases hy : v y with
      | true =>
        have hx : w x = true := by rw [hw x, h]; exact hy
        rw [tested_cons_of_pass hx, List.filterMap_cons_some h, List.filterMap_cons_some h,
          tested_cons_of_pass hy]
        rfl
      | false =>
        have hx : w x = false := by rw [hw x, h]; exact hy
        rw [tested_cons_of_fail hx, List.filterMap_cons_some h, List.filterMap_cons_some h,
          tested_cons_of_fail hy, ih]
