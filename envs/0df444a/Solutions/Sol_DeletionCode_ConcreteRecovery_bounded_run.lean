-- Prove2me | solution 1 for DeletionCode.ConcreteRecovery.bounded_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:59:05.264283+00:00
-- url     : https://prove2.me/submissions/c725ddb1-132c-4646-9a07-529ef00865e3

import Definitions.Def_DeletionCode_ConcreteProgress
import Definitions.Def_DeletionCode_ConcreteInitialization
import Definitions.Def_DeletionCode_ConcreteRecovery
import Theorems.Thm_DeletionCode_ConcreteProgress_lift_step
import Theorems.Thm_DeletionCode_Recovery_State_score_le
import Theorems.Thm_DeletionCode_Recovery_progress
import Theorems.Thm_DeletionCode_Recovery_step_score


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteRecovery
open Windows PartialWords HeaderRecovery SelectedWindows ConcreteDecoder ConcreteModel
variable {B : Type*} [Fintype B] [DecidableEq B]
variable {x : Letters} {n k : ℕ}
namespace DeletionCode.ConcreteRecovery
theorem _root_.solution (M : Model B x n k) (hx : KUnique x n k)
    (s : Recovery.State B) (mem : Bank B) (hi : M.Invariant s mem) :
    ∃ instructions mem' q,
      run x n k M.header mem instructions = some mem' ∧
      M.Invariant q mem' ∧ (∀ b, q.Complete b) ∧
      instructions.length + s.score ≤ 4 * Fintype.card B := by
  classical
  let N := 4 * Fintype.card B
  have aux : ∀ d : ℕ, ∀ s : Recovery.State B, ∀ mem : Bank B,
      N - s.score = d → M.Invariant s mem →
      ∃ instructions mem' q,
        run x n k M.header mem instructions = some mem' ∧
        M.Invariant q mem' ∧ (∀ b, q.Complete b) ∧
        instructions.length + s.score ≤ N := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro s mem hd hi
      by_cases hdone : ∀ b, s.Complete b
      · refine ⟨[], mem, s, rfl, hi, hdone, ?_⟩
        simpa [N] using Recovery.State.score_le s
      · obtain ⟨q, hstep⟩ := Recovery.progress M.schedule s hi.wellFormed hdone
        obtain ⟨q', mem', instruction, hstep', hexec, hinv⟩ :=
          ConcreteProgress.lift_step M hx s mem hi hstep
        have hscore : q'.score = s.score + 1 := Recovery.step_score M.schedule hstep'
        have hbound : q'.score ≤ N := Recovery.State.score_le q'
        have hlt : N - q'.score < d := by omega
        obtain ⟨instructions, mem'', q'', hrun, hfinal, hcomplete, hcost⟩ :=
          ih (N - q'.score) hlt q' mem' rfl hinv
        refine ⟨instruction :: instructions, mem'', q'', ?_, hfinal, hcomplete, ?_⟩
        · simp only [run, hexec, Option.bind_some]
          exact hrun
        · simp only [List.length_cons]
          omega
  exact aux (N - s.score) s mem rfl hi
end DeletionCode.ConcreteRecovery
