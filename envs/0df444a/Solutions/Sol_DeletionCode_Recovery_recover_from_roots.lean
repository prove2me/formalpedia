-- Prove2me | solution 1 for DeletionCode.Recovery.recover_from_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:21.637599+00:00
-- url     : https://prove2.me/submissions/a8a70a81-72c1-4672-9c7f-33ae3c88db92

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery
import Theorems.Thm_DeletionCode_Recovery_bounded_recovery
import Theorems.Thm_DeletionCode_Recovery_initial_wellFormed

set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open State
variable [Fintype B]
namespace DeletionCode.Recovery
theorem _root_.solution (M : Data B) :
    ∃ m s', Trace M m (initial M) s' ∧ (∀ b, s'.Complete b) ∧
      m ≤ 4 * Fintype.card B := by
  obtain ⟨m, s', ht, hc, hm⟩ :=
    bounded_recovery M (initial M) (initial_wellFormed M)
  exact ⟨m, s', ht, hc, by omega⟩
end DeletionCode.Recovery
