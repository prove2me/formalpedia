-- Prove2me | solution 1 for DeletionCode.Recovery.State.start_wellFormed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:51:46.745039+00:00
-- url     : https://prove2.me/submissions/4a7c250a-0f2a-47a7-ab5d-04e15efd0a34

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery
import Theorems.Thm_DeletionCode_Recovery_State_started_start_mono
import Theorems.Thm_DeletionCode_Recovery_State_complete_start

set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open DeletionCode.Recovery.State
namespace DeletionCode.Recovery.State
theorem _root_.solution (M : Data B) (s : State B)
    (hs : WellFormed M s) (b : B) (w : Slot) :
    WellFormed M (s.start b w) := by
  constructor
  · intro a v hav
    exact started_start_mono s b a w (hs.1 a v hav)
  · intro a ha
    exact complete_start s b a w (hs.2 a ha)
end DeletionCode.Recovery.State
