-- Prove2me | solution 1 for FirstPassageLinearTransport.bernoulliAverage_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:28:00.739726+00:00
-- url     : https://prove2.me/submissions/3a47c27b-09e4-4497-bae6-dfe3b54e3095

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p a₀ a₁ b₀ b₁ : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (h₀ : a₀ ≤ b₀) (h₁ : a₁ ≤ b₁) :
    bernoulliAverage p a₀ a₁ ≤ bernoulliAverage p b₀ b₁ := by
  unfold bernoulliAverage
  exact add_le_add
    (mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr hp₁))
    (mul_le_mul_of_nonneg_left h₁ hp₀)
end FirstPassageLinearTransport
