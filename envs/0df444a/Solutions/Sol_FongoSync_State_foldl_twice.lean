-- Prove2me | solution 1 for FongoSync.State.foldl_twice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:42.047941+00:00
-- url     : https://prove2.me/submissions/61df0f90-975d-48e5-8fc6-377c25bd9980

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
import Theorems.Thm_FongoSync_State_apply_twice
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
theorem _root_.solution (σ : String → String → Strategy) (st : State V)
    (pre post : List (Change V)) (a : Change V) :
    (pre ++ a :: a :: post).foldl (State.apply σ) st =
      (pre ++ a :: post).foldl (State.apply σ) st := by
  simp only [List.foldl_append, List.foldl_cons, State.apply_twice]
end State
end FongoSync
