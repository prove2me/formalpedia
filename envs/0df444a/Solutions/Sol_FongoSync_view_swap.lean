-- Prove2me | solution 1 for FongoSync.view_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:05:31.713639+00:00
-- url     : https://prove2.me/submissions/709c5427-0e20-4ef7-9d10-86cdb914824c

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
import Theorems.Thm_FongoSync_view_from_inputs
import Theorems.Thm_FongoSync_inputs_eq
import Theorems.Thm_FongoSync_step_swap

set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false
namespace FongoSync
theorem _root_.solution (sc : Schema) (pre post : List (Change Value)) (a b : Change Value)
    (h : a.field = ALIAS ∨ b.field = ALIAS ∨ Compatible a b) :
    view sc (pre ++ a :: b :: post) = view sc (pre ++ b :: a :: post) := by
  apply view_from_inputs
  apply inputs_eq
  · intro c; simp only [List.mem_append, List.mem_cons]
    constructor <;> rintro (h | h | h | h) <;> simp [h]
  · simp only [registers, List.foldl_append, List.foldl_cons]
    rw [step_swap sc _ a b h]
end FongoSync
