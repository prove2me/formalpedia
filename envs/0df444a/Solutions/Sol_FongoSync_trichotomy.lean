-- Prove2me | solution 1 for FongoSync.trichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:02.295595+00:00
-- url     : https://prove2.me/submissions/ca2e7d44-7fec-4277-a2ab-d805bb588155

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
theorem _root_.solution {x y : E} (inj : key x = key y → x = y) :
    cmp (key x) (key y) = .lt ∨ x = y ∨ cmp (key y) (key x) = .lt := by
  cases hxy : cmp (key x) (key y) with
  | lt => exact .inl rfl
  | eq => exact .inr (.inl (inj (LawfulEqCmp.eq_of_compare hxy)))
  | gt => exact .inr (.inr (OrientedCmp.lt_of_gt hxy))
end FongoSync
