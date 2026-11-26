-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzMiddleInterval_support_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:01.891636+00:00
-- url     : https://prove2.me/submissions/e9c8a71e-1f39-468f-b8ca-b662c8ef5bd7

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_wordIncrementSum_collatz
import Theorems.Thm_FirstPassageLinearTransport_collatz_support_unique_in_unit_interval

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r : ℕ} {a : ℝ} {v w : Fin r → Bool}
    (hv : collatzMiddleInterval a v)
    (hw : collatzMiddleInterval a w) :
    (boolSupport v).card = (boolSupport w).card := by
  unfold collatzMiddleInterval at hv hw
  rw [wordIncrementSum_collatz] at hv hw
  apply collatz_support_unique_in_unit_interval
      (a := a + (r : ℝ) * Real.log 2)
  · linarith [hv.1]
  · linarith [hv.2]
  · linarith [hw.1]
  · linarith [hw.2]
end FirstPassageLinearTransport
