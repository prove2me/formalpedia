-- Prove2me | solution 1 for CohnElkies.upperGammaCenteredKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/cefb2539-2add-46b2-90fa-6bae2219ae8e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaVarianceDensity_integrable
import Theorems.Thm_CohnElkies_upperGammaThirdMomentDensity_integrable
import Theorems.Thm_CohnElkies_upperGammaMeasureDensity_pos
import Theorems.Thm_CohnElkies_upperImaginaryExp_centered_norm_le

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
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    IntegrableOn (upperGammaCenteredKernel ℓ η T)
      (Ioi 0) := by
  have hvariance :=
    upperGammaVarianceDensity_integrable hℓ hη
  have hthird :=
    upperGammaThirdMomentDensity_integrable hℓ hη
  have hmajor : IntegrableOn
      (fun a : ℝ =>
        (T ^ 2 / 2) *
            (a ^ 2 * upperGammaMeasureDensity ℓ η a) +
          (|T| ^ 3 / 6) *
            (a ^ 3 * upperGammaMeasureDensity ℓ η a))
      (Ioi 0) :=
    (hvariance.const_mul (T ^ 2 / 2)).add
      (hthird.const_mul (|T| ^ 3 / 6))
  have hmeas : Measurable
      (upperGammaCenteredKernel ℓ η T) := by
    unfold upperGammaCenteredKernel upperImaginaryExp
      upperGammaMeasureDensity
    fun_prop
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi]
    with a ha
  have hdensity :=
    upperGammaMeasureDensity_pos (η := η) hℓ ha
  unfold upperGammaCenteredKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hdensity]
  calc
    ‖upperImaginaryExp (a * T) - 1 -
        Complex.I * ((a * T : ℝ) : ℂ)‖ *
          upperGammaMeasureDensity ℓ η a ≤
      ((a * T) ^ 2 / 2 + |a * T| ^ 3 / 6) *
        upperGammaMeasureDensity ℓ η a :=
      mul_le_mul_of_nonneg_right
        (upperImaginaryExp_centered_norm_le (a * T))
        hdensity.le
    _ = (T ^ 2 / 2) *
            (a ^ 2 * upperGammaMeasureDensity ℓ η a) +
          (|T| ^ 3 / 6) *
            (a ^ 3 * upperGammaMeasureDensity ℓ η a) := by
      rw [abs_mul, abs_of_pos ha]
      ring
end CohnElkies
