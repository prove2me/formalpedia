-- Prove2me | solution 1 for DeletionCode.Recovery.step_score
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:52:04.156288+00:00
-- url     : https://prove2.me/submissions/84f7555a-0569-4f55-b922-2cb2321f1f3b

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery
import Theorems.Thm_DeletionCode_Recovery_State_score_start
import Theorems.Thm_DeletionCode_Recovery_State_score_fill

set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open State
variable [Fintype B]
namespace DeletionCode.Recovery
theorem _root_.solution (M : Data B) {s s' : State B}
    (h : Step M s s') : s'.score = s.score + 1 := by
  cases h with
  | startAdjacent a b w ha hab hb => exact State.score_start s b w hb
  | startSupplier b a w v hr hn hsrc ha => exact State.score_start s a v ha
  | fillBase b w hr hn hsrc => exact State.score_fill s b w hn
  | fillSupplier b a w hr hn hsrc ha => exact State.score_fill s b w hn
end DeletionCode.Recovery
