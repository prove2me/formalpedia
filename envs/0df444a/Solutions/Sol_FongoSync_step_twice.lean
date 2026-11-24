-- Prove2me | solution 1 for FongoSync.step_twice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:42.480157+00:00
-- url     : https://prove2.me/submissions/8703c469-2a51-458b-842b-45a13d0cc256

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
import Theorems.Thm_FongoSync_State_apply_twice
import Theorems.Thm_FongoSync_apply_twice


set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false
namespace FongoSync
theorem _root_.solution (sc : Schema) (st : State Value) (a : Change Value) :
    step sc (step sc st a) a = step sc st a := by
  by_cases ha : a.field = ALIAS
  · simp [step, ha]
  · simp only [step, ha, ↓reduceIte]; exact State.apply_twice _ _ _
end FongoSync
