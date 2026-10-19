-- Prove2me | solution 1 for CohnElkies.upperGammaCubicRemainderKernel_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/fa3db76b-3062-43cb-ace8-9b2225cfbfc6

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaMeasureDensity_pos
import Theorems.Thm_CohnElkies_upperImaginaryExp_quadratic_remainder_norm_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a)
    (T : ℝ) :
    ‖upperGammaCubicRemainderKernel ℓ η T a‖ ≤
      (|T| ^ 3 / 6) *
        (a ^ 3 * upperGammaMeasureDensity ℓ η a) := by
  have hdensity :=
    upperGammaMeasureDensity_pos (η := η) hℓ ha
  unfold upperGammaCubicRemainderKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hdensity]
  calc
    ‖upperImaginaryExp (a * T) - 1 -
        Complex.I * ((a * T : ℝ) : ℂ) +
          (((a * T) ^ 2 / 2 : ℝ) : ℂ)‖ *
            upperGammaMeasureDensity ℓ η a ≤
      (|a * T| ^ 3 / 6) *
        upperGammaMeasureDensity ℓ η a :=
      mul_le_mul_of_nonneg_right
        (upperImaginaryExp_quadratic_remainder_norm_le
          (a * T)) hdensity.le
    _ = (|T| ^ 3 / 6) *
        (a ^ 3 * upperGammaMeasureDensity ℓ η a) := by
      rw [abs_mul, abs_of_pos ha]
      ring
end CohnElkies
