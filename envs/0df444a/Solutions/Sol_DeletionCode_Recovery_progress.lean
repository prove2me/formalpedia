-- Prove2me | solution 1 for DeletionCode.Recovery.progress
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:52:49.606521+00:00
-- url     : https://prove2.me/submissions/36503fd2-9bd5-493f-9e14-8afecb2bb296

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery
import Theorems.Thm_DeletionCode_Recovery_terminal_complete

set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open State
namespace DeletionCode.Recovery
theorem _root_.solution (M : Data B) (s : State B)
    (hs : s.WellFormed M) (hincomplete : ¬ ∀ b, s.Complete b) :
    ∃ s', Step M s s' := by
  classical
  by_contra hn
  have hstop : ∀ s', ¬ Step M s s' := by
    intro s' hstep
    exact hn ⟨s', hstep⟩
  exact hincomplete (terminal_complete M s hs hstop)
end DeletionCode.Recovery
