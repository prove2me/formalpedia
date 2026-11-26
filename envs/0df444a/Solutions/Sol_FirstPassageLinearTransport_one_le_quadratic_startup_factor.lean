-- Prove2me | solution 1 for FirstPassageLinearTransport.one_le_quadratic_startup_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:04.600906+00:00
-- url     : https://prove2.me/submissions/a837f61a-e4f4-4a2a-92e2-fd2e9307235b

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_quadratic_startup_exponent_le

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M : ℕ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hsmall : ¬(4 ≤ M ∧ 2 ≤ t * M)) :
    1 ≤ quadraticWindowShellConstant *
      Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) := by
  have hexp := quadratic_startup_exponent_le ht0 ht1 hsmall
  have hnonneg :
      0 ≤ 4 * maximalBarrierC0 - maximalBarrierC0 * t ^ 2 * (M : ℝ) := by
    linarith
  unfold quadraticWindowShellConstant
  have hone :
      1 ≤ Real.exp
        (4 * maximalBarrierC0 - maximalBarrierC0 * t ^ 2 * (M : ℝ)) :=
    Real.one_le_exp hnonneg
  calc
    1 ≤ 2 * Real.exp
        (4 * maximalBarrierC0 - maximalBarrierC0 * t ^ 2 * (M : ℝ)) := by
      nlinarith
    _ = 2 * Real.exp (4 * maximalBarrierC0) *
        Real.exp (-(maximalBarrierC0 * t ^ 2 * (M : ℝ))) := by
      rw [show
        4 * maximalBarrierC0 - maximalBarrierC0 * t ^ 2 * (M : ℝ) =
          4 * maximalBarrierC0 +
            (-(maximalBarrierC0 * t ^ 2 * (M : ℝ))) by ring,
        Real.exp_add]
      ring
end FirstPassageLinearTransport
