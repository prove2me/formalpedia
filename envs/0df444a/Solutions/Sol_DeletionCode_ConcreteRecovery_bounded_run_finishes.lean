-- Prove2me | solution 1 for DeletionCode.ConcreteRecovery.bounded_run_finishes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:00:01.664959+00:00
-- url     : https://prove2.me/submissions/df33f2a0-d1b4-4760-8acb-5d720e28fb02

import Definitions.Def_DeletionCode_ConcreteProgress
import Definitions.Def_DeletionCode_ConcreteInitialization
import Definitions.Def_DeletionCode_ConcreteRecovery
import Theorems.Thm_DeletionCode_ConcreteRecovery_bounded_run
import Theorems.Thm_DeletionCode_ConcreteDecoder_finish_correct
import Theorems.Thm_DeletionCode_ConcreteModel_Model_complete_known


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteRecovery
open Windows PartialWords HeaderRecovery SelectedWindows ConcreteDecoder ConcreteModel
variable {B : Type*} [Fintype B] [DecidableEq B]
variable {x : Letters} {n k : ℕ}
namespace DeletionCode.ConcreteRecovery
theorem _root_.solution (M : Model B x n k) (hx : KUnique x n k)
    (s : Recovery.State B) (mem : Bank B) (hi : M.Invariant s mem) :
    ∃ instructions,
      instructions.length + s.score ≤ 4 * Fintype.card B ∧
      (run x n k M.header mem instructions).bind (finish k M.header) =
        some (fun b i => negativePath k (M.header b) (M.long b) i.val) := by
  obtain ⟨instructions, mem', q, hrun, hinv, hdone, hcost⟩ := bounded_run M hx s mem hi
  refine ⟨instructions, hcost, ?_⟩
  rw [hrun]
  simp only [Option.bind_some]
  apply finish_correct k M.header M.long mem' hinv.sound
  intro b
  exact M.complete_known q mem' hinv.realizes b (hdone b)
end DeletionCode.ConcreteRecovery
