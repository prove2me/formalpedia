-- Prove2me | solution 1 for FongoSync.State.apply_twice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:07.641808+00:00
-- url     : https://prove2.me/submissions/ad199c90-b0fe-4fe4-bf77-cb8acaf880b4

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
import Theorems.Thm_FongoSync_apply_twice


set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
namespace State
theorem _root_.solution (σ : String → String → Strategy) (st : State V) (a : Change V) :
    State.apply σ (State.apply σ st a) a = State.apply σ st a := by
  funext k
  simp only [State.apply]
  by_cases ha : k = a.key
  · simp only [ha, ↓reduceIte]; exact FongoSync.apply_twice _ _ _
  · simp [ha]
end State
end FongoSync
