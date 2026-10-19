-- Prove2me | solution 1 for CohnElkies.upperGammaDampingIntegrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/93b96490-d245-4f82-b317-e38a00a0c77f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaVarianceDensity_integrable
import Theorems.Thm_CohnElkies_upperGammaMeasureDensity_pos

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
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    IntegrableOn
      (upperGammaDampingIntegrand ℓ η T) (Ioi 0) := by
  have hvariance := upperGammaVarianceDensity_integrable
    hℓ hη
  have hmajor : IntegrableOn
      (fun a : ℝ => (T ^ 2 / 2) *
        (a ^ 2 * upperGammaMeasureDensity ℓ η a))
      (Ioi 0) :=
    hvariance.const_mul (T ^ 2 / 2)
  have hmeas : Measurable
      (upperGammaDampingIntegrand ℓ η T) := by
    unfold upperGammaDampingIntegrand
      upperGammaMeasureDensity
    fun_prop
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi]
    with a ha
  have hdensity := upperGammaMeasureDensity_pos
    (η := η) hℓ ha
  have hcos :
      0 ≤ 1 - Real.cos (a * T) :=
    sub_nonneg.mpr (Real.cos_le_one _)
  have hquad :
      1 - Real.cos (a * T) ≤ (a * T) ^ 2 / 2 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos
      (x := a * T)]
  unfold upperGammaDampingIntegrand
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hcos hdensity.le)]
  calc
    (1 - Real.cos (a * T)) *
        upperGammaMeasureDensity ℓ η a ≤
      ((a * T) ^ 2 / 2) *
        upperGammaMeasureDensity ℓ η a :=
      mul_le_mul_of_nonneg_right hquad hdensity.le
    _ = (T ^ 2 / 2) *
        (a ^ 2 * upperGammaMeasureDensity ℓ η a) := by
      ring
end CohnElkies
