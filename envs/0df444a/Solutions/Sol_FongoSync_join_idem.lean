-- Prove2me | solution 1 for FongoSync.join_idem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:13.698143+00:00
-- url     : https://prove2.me/submissions/542b3d02-2d0c-4154-b96f-83115ad7caaf

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
theorem _root_.solution (a : Option E) : join cmp key a a = a := by
  cases a with
  | none => rfl
  | some e => simp [join, keep, ReflCmp.compare_self]
end FongoSync
