-- Prove2me | solution 1 for FirstPassageLinearTransport.bernoulliAverage_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:27:49.559776+00:00
-- url     : https://prove2.me/submissions/37ead979-7706-49de-a90f-810e762a6240

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p x₀ x₁ : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hx₀ : x₀ ≤ 1) (hx₁ : x₁ ≤ 1) :
    bernoulliAverage p x₀ x₁ ≤ 1 := by
  unfold bernoulliAverage
  nlinarith
end FirstPassageLinearTransport
