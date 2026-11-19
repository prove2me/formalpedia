-- Prove2me | solution 1 for DeletionCode.Recovery.State.started_start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:50:47.975814+00:00
-- url     : https://prove2.me/submissions/3d946742-bb35-452d-a704-d12815178690

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery

set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open DeletionCode.Recovery.State
namespace DeletionCode.Recovery.State
theorem _root_.solution (s : State B) (b : B) (w : Slot) :
    (s.start b w).Started b := by simp [Started, start]
end DeletionCode.Recovery.State
