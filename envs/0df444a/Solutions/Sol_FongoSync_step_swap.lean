-- Prove2me | solution 1 for FongoSync.step_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:21.513202+00:00
-- url     : https://prove2.me/submissions/c1773031-a90e-4f49-bcfa-b0ac34593c38

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
import Theorems.Thm_FongoSync_State_apply_swap


set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false
namespace FongoSync
theorem _root_.solution (sc : Schema) (st : State Value) (a b : Change Value)
    (h : a.field = ALIAS ∨ b.field = ALIAS ∨ Compatible a b) :
    step sc (step sc st a) b = step sc (step sc st b) a := by
  by_cases ha : a.field = ALIAS
  · simp [step, ha]
  · by_cases hb : b.field = ALIAS
    · simp [step, hb]
    · simp only [step, ha, hb, ↓reduceIte]
      exact State.apply_swap _ _ _ _ (by simpa [ha, hb] using h)
end FongoSync
