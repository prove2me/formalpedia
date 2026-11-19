-- Prove2me | solution 1 for DeletionCode.Recovery.State.score_fill
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:51:32.001398+00:00
-- url     : https://prove2.me/submissions/16c39257-f210-41bb-b670-70224c155ae2

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery

set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open State
variable [Fintype B]
open DeletionCode.Recovery.State
namespace DeletionCode.Recovery.State
theorem _root_.solution (s : State B) (b : B) (w : Slot)
    (hn : ¬ s.Done b w) : (s.fill b w).score = s.score + 1 := by
  have hnot : (b, w) ∉ s.filled := hn
  change s.startedSet.card + (insert (b, w) s.filled).card = s.score + 1
  rw [Finset.card_insert_of_notMem hnot]
  unfold score
  omega
end DeletionCode.Recovery.State
