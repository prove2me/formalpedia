-- Prove2me | solution 1 for DeletionCode.Recovery.terminal_started_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:51:42.080178+00:00
-- url     : https://prove2.me/submissions/8d7c3bb2-578e-4a1f-93c7-a45aa642f774

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery
import Theorems.Thm_DeletionCode_Recovery_State_frontier

set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open State
namespace DeletionCode.Recovery
theorem _root_.solution (M : Data B) (s : State B)
    (hstop : ∀ s', ¬ Step M s s') : ∀ b, s.Started b → s.Complete b := by
  classical
  have aux : ∀ r : ℕ, ∀ b, M.rank b = r → s.Started b → s.Complete b := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro b hr hb
      by_contra hnot
      obtain ⟨w, hw, hmissing⟩ := State.frontier s b hb hnot
      cases hsrc : M.source b w with
      | none => exact hstop _ (Step.fillBase s b w hw hmissing hsrc)
      | some a =>
        by_cases ha : s.Started a
        · have hsmall : M.rank a < r := by
            have he := M.earlier b w a hsrc
            omega
          have hac : s.Complete a := ih (M.rank a) hsmall a rfl ha
          exact hstop _ (Step.fillSupplier s b a w hw hmissing hsrc hac)
        · exact hstop _ (Step.startSupplier s b a w 0 hw hmissing hsrc ha)
  intro b hb
  exact aux (M.rank b) b rfl hb
end DeletionCode.Recovery
