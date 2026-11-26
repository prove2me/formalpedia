-- Prove2me | solution 1 for FirstPassageLinearTransport.tiltedBinomialMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:31:35.62699+00:00
-- url     : https://prove2.me/submissions/cbc0f7de-ba58-4c9d-acff-aba8f803606c

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (n k : ℕ) :
    0 ≤ tiltedBinomialMass p n k := by
  unfold tiltedBinomialMass
  exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hp₀ _))
    (pow_nonneg (sub_nonneg.mpr hp₁) _)
end FirstPassageLinearTransport
