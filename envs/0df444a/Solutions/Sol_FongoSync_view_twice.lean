-- Prove2me | solution 1 for FongoSync.view_twice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:05:34.79272+00:00
-- url     : https://prove2.me/submissions/1abfffba-1d8a-470d-b961-561dd2991c2e

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
import Theorems.Thm_FongoSync_view_from_inputs
import Theorems.Thm_FongoSync_inputs_eq
import Theorems.Thm_FongoSync_step_twice

set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false
namespace FongoSync
theorem _root_.solution (sc : Schema) (pre post : List (Change Value)) (a : Change Value) :
    view sc (pre ++ a :: a :: post) = view sc (pre ++ a :: post) := by
  apply view_from_inputs
  apply inputs_eq
  · intro c; simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (h | h | h | h) <;> simp [h]
    · rintro (h | h | h) <;> simp [h]
  · simp only [registers, List.foldl_append, List.foldl_cons]
    rw [step_twice]
end FongoSync
