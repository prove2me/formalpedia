-- Prove2me | solution 1 for CohnElkies.upperGammaCenteredPhase_cubic_remainder_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/a20036f1-3fa6-4e14-a740-7cba8aa27958

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaThirdMomentDensity_integrable
import Theorems.Thm_CohnElkies_upperGammaCubicRemainderKernel_norm_le
import Theorems.Thm_CohnElkies_upperGammaCenteredPhase_add_quadratic_eq_integral

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
    ‖upperGammaCenteredPhase ℓ η T +
        ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ)‖ ≤
      (ℓ * upperGammaThirdMoment ℓ η / 6) * |T| ^ 3 := by
  have hmajor : IntegrableOn
      (fun a : ℝ =>
        (|T| ^ 3 / 6) *
          (a ^ 3 * upperGammaMeasureDensity ℓ η a))
      (Ioi 0) :=
    (upperGammaThirdMomentDensity_integrable hℓ hη).const_mul
      (|T| ^ 3 / 6)
  have hpoint :
      ∀ᵐ a : ℝ ∂volume.restrict (Ioi 0),
        ‖upperGammaCubicRemainderKernel ℓ η T a‖ ≤
          (|T| ^ 3 / 6) *
            (a ^ 3 * upperGammaMeasureDensity ℓ η a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    exact upperGammaCubicRemainderKernel_norm_le hℓ ha T
  calc
    ‖upperGammaCenteredPhase ℓ η T +
        ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ)‖ =
      ‖∫ a : ℝ in Ioi 0,
        upperGammaCubicRemainderKernel ℓ η T a‖ := by
          rw [upperGammaCenteredPhase_add_quadratic_eq_integral
            hℓ hη T]
    _ ≤ ∫ a : ℝ in Ioi 0,
        (|T| ^ 3 / 6) *
          (a ^ 3 * upperGammaMeasureDensity ℓ η a) :=
      MeasureTheory.norm_integral_le_of_norm_le hmajor hpoint
    _ = (|T| ^ 3 / 6) *
        (∫ a : ℝ in Ioi 0,
          a ^ 3 * upperGammaMeasureDensity ℓ η a) := by
      rw [MeasureTheory.integral_const_mul]
    _ = (ℓ * upperGammaThirdMoment ℓ η / 6) * |T| ^ 3 := by
      unfold upperGammaThirdMoment
      field_simp [hℓ.ne']
end CohnElkies
