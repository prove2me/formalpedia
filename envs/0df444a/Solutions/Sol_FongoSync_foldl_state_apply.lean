-- Prove2me | solution 1 for FongoSync.foldl_state_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:49.925383+00:00
-- url     : https://prove2.me/submissions/e96bf9bf-e3ea-4efb-8f97-8c2d82b374df

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
namespace FongoSync
theorem _root_.solution (σ : String → String → Strategy) (cs : List (Change V)) (st : State V)
    (k : Key) :
    (cs.foldl (State.apply σ) st) k = (entriesAt cs k).foldl (apply (strategyAt σ k)) (st k) := by
  induction cs generalizing st with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl, ih, entriesAt]
    by_cases h : c.key = k
    · simp [List.filter, h, State.apply]
    · have h' : k ≠ c.key := fun e => h e.symm
      simp [List.filter, h, h', State.apply]
end FongoSync
