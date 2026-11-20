-- Prove2me | solution 1 for DeletionCode.ConcreteRecovery.decode_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:00:59.453202+00:00
-- url     : https://prove2.me/submissions/21ced859-53fa-415a-8123-5eb5d4188ecf

import Definitions.Def_DeletionCode_ConcreteProgress
import Definitions.Def_DeletionCode_ConcreteInitialization
import Definitions.Def_DeletionCode_ConcreteRecovery
import Theorems.Thm_DeletionCode_ConcreteRecovery_bounded_run_finishes
import Theorems.Thm_DeletionCode_ConcreteInitialization_initialization_exists


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteRecovery
open Windows PartialWords HeaderRecovery SelectedWindows ConcreteDecoder ConcreteModel
variable {B : Type*} [Fintype B] [DecidableEq B]
variable {x : Letters} {n k : ℕ}
namespace DeletionCode.ConcreteRecovery
theorem _root_.solution (M : Model B x n k) (hx : KUnique x n k) :
    ∃ roots instructions,
      roots.length = ConcreteInitialization.rootCount M ∧
      instructions.length ≤ 4 * Fintype.card B ∧
      decode x n k M.header roots instructions =
        some (fun b i => negativePath k (M.header b) (M.long b) i.val) := by
  obtain ⟨roots, mem, hroots, hload, hi⟩ := ConcreteInitialization.initialization_exists M
  obtain ⟨instructions, hcost, hrun⟩ :=
    bounded_run_finishes M hx (Recovery.initial M.schedule) mem hi
  refine ⟨roots, instructions, hroots, by omega, ?_⟩
  simp only [decode, hload, Option.bind_some]
  exact hrun
end DeletionCode.ConcreteRecovery
