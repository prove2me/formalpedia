-- Prove2me | solution 1 for CohnElkies.upperGammaThirdMomentDensity_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/7946f261-4070-4997-a191-9c5d1a437878

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upper_laplace_monomial_integrable
import Theorems.Thm_CohnElkies_upperGammaThirdMomentDensity_pointwise_bounds

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
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) :
    IntegrableOn
      (fun a : ℝ => a ^ 3 * upperGammaMeasureDensity ℓ η a)
      (Set.Ioi 0) := by
  have hone := upper_laplace_monomial_integrable hη 1
  have htwo := upper_laplace_monomial_integrable hη 2
  have hsum := htwo.add (hone.const_mul (ℓ / 2))
  have hmajor : IntegrableOn
      (fun a : ℝ =>
        (a ^ 2 + (ℓ / 2) * a) * Real.exp (-η * a))
      (Set.Ioi 0) := by
    apply hsum.congr_fun _ measurableSet_Ioi
    intro a ha
    change a ^ 2 * Real.exp (-η * a) +
      (ℓ / 2) * (a ^ 1 * Real.exp (-η * a)) =
        (a ^ 2 + (ℓ / 2) * a) * Real.exp (-η * a)
    simp
    ring
  have hmeas : Measurable
      (fun a : ℝ => a ^ 3 * upperGammaMeasureDensity ℓ η a) := by
    unfold upperGammaMeasureDensity
    fun_prop
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi]
    with a ha
  have hapos : 0 < a := ha
  have hbounds := upperGammaThirdMomentDensity_pointwise_bounds
    (η := η) hℓ hapos
  have hpositive :
      0 ≤ a ^ 3 * upperGammaMeasureDensity ℓ η a :=
    (show 0 ≤ (ℓ / 2) * a * Real.exp (-η * a) by
      positivity).trans hbounds.1
  rw [Real.norm_eq_abs, abs_of_nonneg hpositive]
  exact hbounds.2
end CohnElkies
