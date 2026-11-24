-- Prove2me | solution 1 for FongoSync.isLE_of_not_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:00:06.786245+00:00
-- url     : https://prove2.me/submissions/b7e0eecb-d47e-4efa-9f5c-eb3f3da00ac0

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {E K : Type} (cmp : K → K → Ordering) (key : E → K)
variable [TransCmp cmp] [LawfulEqCmp cmp]
variable {cmp key}
namespace FongoSync
theorem _root_.solution {x y : K} (h : cmp x y ≠ .lt) : (cmp y x).isLE := by
  cases h' : cmp y x with
  | lt => rfl
  | eq => rfl
  | gt => exact absurd (OrientedCmp.lt_of_gt h') h
end FongoSync
