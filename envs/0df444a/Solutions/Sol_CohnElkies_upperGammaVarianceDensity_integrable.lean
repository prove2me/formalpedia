-- Prove2me | solution 1 for CohnElkies.upperGammaVarianceDensity_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/5e9172a4-9dbe-4889-9d16-24ea17f15bad

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upper_laplace_monomial_integrable
import Theorems.Thm_CohnElkies_upperGammaVarianceDensity_pointwise_bounds

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
      (fun a : ℝ => a ^ 2 * upperGammaMeasureDensity ℓ η a)
      (Set.Ioi 0) := by
  have hzero := upper_laplace_monomial_integrable hη 0
  have hone := upper_laplace_monomial_integrable hη 1
  have hsum := hone.add (hzero.const_mul (ℓ / 2))
  have hmajor : IntegrableOn
      (fun a : ℝ => (a + ℓ / 2) * Real.exp (-η * a))
      (Set.Ioi 0) := by
    apply hsum.congr_fun _ measurableSet_Ioi
    intro a ha
    change a ^ 1 * Real.exp (-η * a) +
      (ℓ / 2) * (a ^ 0 * Real.exp (-η * a)) =
        (a + ℓ / 2) * Real.exp (-η * a)
    simp
    ring
  have hmeas : Measurable
      (fun a : ℝ => a ^ 2 * upperGammaMeasureDensity ℓ η a) := by
    unfold upperGammaMeasureDensity
    fun_prop
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi]
    with a ha
  have hbounds := upperGammaVarianceDensity_pointwise_bounds
    (η := η) hℓ ha
  have hpositive :
      0 ≤ a ^ 2 * upperGammaMeasureDensity ℓ η a :=
    (show 0 ≤ (ℓ / 2) * Real.exp (-η * a) by positivity).trans
      hbounds.1
  rw [Real.norm_eq_abs, abs_of_nonneg hpositive]
  exact hbounds.2
end CohnElkies
