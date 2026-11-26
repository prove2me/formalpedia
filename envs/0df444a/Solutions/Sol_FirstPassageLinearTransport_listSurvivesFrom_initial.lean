-- Prove2me | solution 1 for FirstPassageLinearTransport.listSurvivesFrom_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:33:16.989119+00:00
-- url     : https://prove2.me/submissions/4e21f9ee-5388-45f3-b59e-00537fd5a7cd

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {lo z : ℝ} {x : Bool → ℝ} {l : List Bool}
    (h : listSurvivesFrom lo x z l) : lo ≤ z := by
  cases l with
  | nil => exact h
  | cons b l => exact h.1
end FirstPassageLinearTransport
