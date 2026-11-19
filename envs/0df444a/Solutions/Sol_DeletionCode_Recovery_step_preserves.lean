-- Prove2me | solution 1 for DeletionCode.Recovery.step_preserves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:52:16.633995+00:00
-- url     : https://prove2.me/submissions/8c0a8d53-79d8-4b2d-a894-124bc1e26b60

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery
import Theorems.Thm_DeletionCode_Recovery_State_ready_started
import Theorems.Thm_DeletionCode_Recovery_State_start_wellFormed
import Theorems.Thm_DeletionCode_Recovery_State_fill_wellFormed

set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open State
namespace DeletionCode.Recovery
theorem _root_.solution (M : Data B) {s s' : State B}
    (h : Step M s s') (hs : s.WellFormed M) : s'.WellFormed M := by
  cases h with
  | startAdjacent a b w ha hab hb =>
      exact State.start_wellFormed M s hs b w
  | startSupplier b a w v hr hn hsrc ha =>
      exact State.start_wellFormed M s hs a v
  | fillBase b w hr hn hsrc =>
      exact State.fill_wellFormed M s hs b w
        (State.ready_started M s hs b w hr)
  | fillSupplier b a w hr hn hsrc ha =>
      exact State.fill_wellFormed M s hs b w
        (State.ready_started M s hs b w hr)
end DeletionCode.Recovery
