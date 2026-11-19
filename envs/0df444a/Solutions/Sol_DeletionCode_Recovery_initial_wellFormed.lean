-- Prove2me | solution 1 for DeletionCode.Recovery.initial_wellFormed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:11:00.57841+00:00
-- url     : https://prove2.me/submissions/3896ae2f-bf10-4cdd-949f-cc72bfa3e4af

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
namespace DeletionCode.Recovery
theorem _root_.solution (M : Data B) : (initial M).WellFormed M := by
  classical
  constructor
  · intro b w h
    have hr : M.root b := by simpa [State.Done, initial] using h
    simp [State.Started, initial, hr]
  · intro b hr w
    simp [State.Done, initial, hr]
end DeletionCode.Recovery
