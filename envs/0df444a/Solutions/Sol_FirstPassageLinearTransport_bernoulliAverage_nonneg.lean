-- Prove2me | solution 1 for FirstPassageLinearTransport.bernoulliAverage_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:28:24.92726+00:00
-- url     : https://prove2.me/submissions/54f55a7b-42c7-40b6-afcd-95c2a9dcf158

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
    (hx₀ : 0 ≤ x₀) (hx₁ : 0 ≤ x₁) :
    0 ≤ bernoulliAverage p x₀ x₁ := by
  unfold bernoulliAverage
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr hp₁) hx₀)
    (mul_nonneg hp₀ hx₁)
end FirstPassageLinearTransport
