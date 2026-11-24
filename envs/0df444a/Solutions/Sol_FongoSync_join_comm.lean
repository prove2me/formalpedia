-- Prove2me | solution 1 for FongoSync.join_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:18.256372+00:00
-- url     : https://prove2.me/submissions/c5de1c5b-7e4a-44c3-bb00-d5a2bddaf9d5

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
theorem _root_.solution (a b : Option E) (inj : ∀ x ∈ a, ∀ y ∈ b, key x = key y → x = y) :
    join cmp key a b = join cmp key b a := by
  cases a with
  | none => cases b <;> rfl
  | some x =>
    cases b with
    | none => rfl
    | some y =>
      have := keep_swap (cmp := cmp) (key := key) none x y (inj x rfl y rfl)
      simpa [join, keep] using this
end FongoSync
