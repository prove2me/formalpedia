-- Prove2me | solution 1 for FongoSync.join_none_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:29.560736+00:00
-- url     : https://prove2.me/submissions/380c2706-ad17-4b26-b3eb-2723babd20da

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
theorem _root_.solution (b : Option E) : join cmp key none b = b := by
  cases b <;> rfl
end FongoSync
