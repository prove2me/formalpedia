-- Prove2me | solution 1 for DeletionCode.Recovery.State.started_start_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:51:16.712476+00:00
-- url     : https://prove2.me/submissions/83f85f40-e960-4762-81ae-26ed6ce815e8

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery
import Theorems.Thm_DeletionCode_Recovery_State_started_start

set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open DeletionCode.Recovery.State
namespace DeletionCode.Recovery.State
theorem _root_.solution (s : State B) (b a : B) (w : Slot)
    (h : s.Started a) : (s.start b w).Started a := by
  by_cases hab : a = b
  · subst a
    exact started_start s b w
  · have hba : b ≠ a := Ne.symm hab
    simpa [Started, start, hab, hba] using h
end DeletionCode.Recovery.State
