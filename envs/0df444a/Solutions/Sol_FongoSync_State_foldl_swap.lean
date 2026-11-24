-- Prove2me | solution 1 for FongoSync.State.foldl_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:17.576498+00:00
-- url     : https://prove2.me/submissions/07f9c623-b7a2-4ac5-9b45-815fc3da4974

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
import Theorems.Thm_FongoSync_State_apply_swap

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
    (pre post : List (Change V)) (a b : Change V) (h : Compatible a b) :
    (pre ++ a :: b :: post).foldl (State.apply σ) st =
      (pre ++ b :: a :: post).foldl (State.apply σ) st := by
  simp only [List.foldl_append, List.foldl_cons, State.apply_swap σ _ a b h]
end State
end FongoSync
