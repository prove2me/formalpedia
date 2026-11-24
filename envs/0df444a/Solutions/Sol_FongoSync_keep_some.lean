-- Prove2me | solution 1 for FongoSync.keep_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:59:59.660122+00:00
-- url     : https://prove2.me/submissions/17808779-3584-4689-9b5a-0699138b8451

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
theorem _root_.solution (h : Option E) (e : E) : ∃ m, keep cmp key h e = some m := by
  cases h with
  | none => exact ⟨e, rfl⟩
  | some s => rw [keep_held]; split <;> exact ⟨_, rfl⟩
end FongoSync
