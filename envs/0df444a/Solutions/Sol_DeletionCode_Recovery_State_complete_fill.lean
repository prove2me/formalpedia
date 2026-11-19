-- Prove2me | solution 1 for DeletionCode.Recovery.State.complete_fill
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:50:56.827517+00:00
-- url     : https://prove2.me/submissions/f0878812-ca8d-451c-a461-570e7af61c7b

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
theorem _root_.solution (s : State B) (b a : B) (w : Slot)
    (h : s.Complete a) : (s.fill b w).Complete a := by
  intro v
  exact Finset.mem_insert_of_mem (h v)
end DeletionCode.Recovery.State
