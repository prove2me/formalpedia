-- Prove2me | solution 1 for FongoSync.join_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:55.088881+00:00
-- url     : https://prove2.me/submissions/28cbeb5d-ce25-4a26-8383-f89e05ef3b13

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_isLE_of_not_lt
import Theorems.Thm_FongoSync_join_none_left

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {E K : Type} (cmp : K → K → Ordering) (key : E → K)
variable [TransCmp cmp] [LawfulEqCmp cmp]
variable {cmp key}
namespace FongoSync
theorem _root_.solution (a b c : Option E) :
    join cmp key (join cmp key a b) c = join cmp key a (join cmp key b c) := by
  cases a with
  | none => simp only [join_none_left]
  | some x =>
    cases b with
    | none => cases c <;> rfl
    | some y =>
      cases c with
      | none => rfl
      | some z =>
        simp only [join, keep_held]
        by_cases hyz : cmp (key y) (key z) = .lt
        · by_cases hxy : cmp (key x) (key y) = .lt
          · simp [hxy, hyz, TransCmp.lt_trans hxy hyz]
          · simp [hxy, hyz]
        · by_cases hxy : cmp (key x) (key y) = .lt
          · simp [hxy, hyz]
          · have hzx : (cmp (key z) (key x)).isLE :=
              TransCmp.isLE_trans (isLE_of_not_lt hyz) (isLE_of_not_lt hxy)
            have hxz : cmp (key x) (key z) ≠ .lt := fun h =>
              absurd (TransCmp.lt_of_isLE_of_lt hzx h) (by simp [ReflCmp.compare_self])
            simp [hxy, hyz, hxz]
end FongoSync
