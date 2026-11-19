-- Prove2me | solution 1 for DeletionCode.Recovery.State.score_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:10:33.529936+00:00
-- url     : https://prove2.me/submissions/fdbc3c0c-1bc3-4391-bf43-71aeabe99d42

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
theorem _root_.solution (s : State B) : s.score ≤ 4 * Fintype.card B := by
  have h1 : s.startedSet.card ≤ Fintype.card B := Finset.card_le_univ _
  have h2 : s.filled.card ≤ Fintype.card (B × Slot) := Finset.card_le_univ _
  have h3 : s.filled.card ≤ 3 * Fintype.card B := by
    simpa [Slot, Fintype.card_prod, Nat.mul_comm] using h2
  unfold score
  omega
end DeletionCode.Recovery.State
