-- Prove2me | solution 1 for DeletionCode.Recovery.State.ready_started
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:51:06.355232+00:00
-- url     : https://prove2.me/submissions/b9b88a14-3603-44f2-a2e4-c28a5cd0522a

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery

set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open DeletionCode.Recovery.State
namespace DeletionCode.Recovery.State
theorem _root_.solution (M : Data B) (s : State B)
    (hs : WellFormed M s) (b : B) (w : Slot) (h : s.Ready b w) :
    s.Started b := by
  rcases h with hseed | ⟨v, hv, _⟩
  · simp [Started, hseed]
  · exact hs.1 b v hv
end DeletionCode.Recovery.State
