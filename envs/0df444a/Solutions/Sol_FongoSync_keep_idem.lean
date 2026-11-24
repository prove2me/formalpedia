-- Prove2me | solution 1 for FongoSync.keep_idem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:12.920734+00:00
-- url     : https://prove2.me/submissions/7c6b429a-a94b-4e7f-bdf6-259c6c7fcd7e

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
theorem _root_.solution (h : Option E) (e : E) : keep cmp key (keep cmp key h e) e = keep cmp key h e := by
  cases h with
  | none => simp [ReflCmp.compare_self]
  | some s =>
    by_cases hlt : cmp (key s) (key e) = .lt
    · simp [hlt, ReflCmp.compare_self]
    · simp [hlt]
end FongoSync
