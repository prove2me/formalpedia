-- Prove2me | solution 1 for DeletionCode.Recovery.bounded_recovery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:53:18.159896+00:00
-- url     : https://prove2.me/submissions/8812e864-5676-41f7-8128-b13e62522854

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery
import Theorems.Thm_DeletionCode_Recovery_step_preserves
import Theorems.Thm_DeletionCode_Recovery_progress
import Theorems.Thm_DeletionCode_Recovery_State_score_le
import Theorems.Thm_DeletionCode_Recovery_step_score

set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open State
variable [Fintype B]
namespace DeletionCode.Recovery
theorem _root_.solution (M : Data B) (s : State B)
    (hs : s.WellFormed M) :
    ∃ m s', Trace M m s s' ∧ (∀ b, s'.Complete b) ∧
      m + s.score ≤ 4 * Fintype.card B := by
  classical
  let N := 4 * Fintype.card B
  have aux : ∀ d : ℕ, ∀ q : State B, N - q.score = d → q.WellFormed M →
      ∃ m q', Trace M m q q' ∧ (∀ b, q'.Complete b) ∧ m + q.score ≤ N := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro q hd hq
      by_cases hdone : ∀ b, q.Complete b
      · exact ⟨0, q, Trace.nil q, hdone, by
          have hbound := State.score_le q
          dsimp [N]
          omega⟩
      · obtain ⟨q', hstep⟩ := progress M q hq hdone
        have hq' : q'.WellFormed M := step_preserves M hstep hq
        have hscore : q'.score = q.score + 1 := step_score M hstep
        have hbound : q'.score ≤ N := State.score_le q'
        have hlt : N - q'.score < d := by omega
        obtain ⟨m, q'', htrace, hcomplete, hcost⟩ :=
          ih (N - q'.score) hlt q' rfl hq'
        exact ⟨m + 1, q'', Trace.cons hstep htrace, hcomplete, by omega⟩
  exact aux (N - s.score) s rfl hs
end DeletionCode.Recovery
