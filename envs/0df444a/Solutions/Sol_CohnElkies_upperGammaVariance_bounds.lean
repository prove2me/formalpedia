-- Prove2me | solution 1 for CohnElkies.upperGammaVariance_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/3266bb82-0338-4a1b-a41b-3c08599a5c52

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upper_laplace_monomial_integrable
import Theorems.Thm_CohnElkies_upper_laplace_monomial_integral
import Theorems.Thm_CohnElkies_upperGammaVarianceDensity_pointwise_bounds
import Theorems.Thm_CohnElkies_upperGammaVarianceDensity_integrable

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
    1 / (2 * η) ≤ upperGammaVariance ℓ η ∧
      upperGammaVariance ℓ η ≤
        1 / (2 * η) + 1 / (ℓ * η ^ 2) := by
  have hzero : IntegrableOn
      (fun a : ℝ => Real.exp (-η * a))
      (Set.Ioi 0) := by
    simpa using! upper_laplace_monomial_integrable hη 0
  have hline : IntegrableOn
      (fun a : ℝ => a * Real.exp (-η * a))
      (Set.Ioi 0) := by
    simpa using! upper_laplace_monomial_integrable hη 1
  have hconst : IntegrableOn
      (fun a : ℝ => (ℓ / 2) * Real.exp (-η * a))
      (Set.Ioi 0) :=
    hzero.const_mul (ℓ / 2)
  have hactual := upperGammaVarianceDensity_integrable hℓ hη
  have hmajor : IntegrableOn
      (fun a : ℝ => (a + ℓ / 2) * Real.exp (-η * a))
      (Set.Ioi 0) := by
    apply (hline.add hconst).congr_fun _ measurableSet_Ioi
    intro a ha
    change a * Real.exp (-η * a) +
      (ℓ / 2) * Real.exp (-η * a) =
        (a + ℓ / 2) * Real.exp (-η * a)
    ring
  have hlowerIntegral :
      (∫ a : ℝ in Set.Ioi 0,
        (ℓ / 2) * Real.exp (-η * a)) ≤
        ∫ a : ℝ in Set.Ioi 0,
          a ^ 2 * upperGammaMeasureDensity ℓ η a := by
    apply integral_mono_ae hconst hactual
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    exact (upperGammaVarianceDensity_pointwise_bounds
      (η := η) hℓ ha).1
  have hupperIntegral :
      (∫ a : ℝ in Set.Ioi 0,
        a ^ 2 * upperGammaMeasureDensity ℓ η a) ≤
        ∫ a : ℝ in Set.Ioi 0,
          (a + ℓ / 2) * Real.exp (-η * a) := by
    apply integral_mono_ae hactual hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    exact (upperGammaVarianceDensity_pointwise_bounds
      (η := η) hℓ ha).2
  have hzerovalue :
      (∫ a : ℝ in Set.Ioi 0,
        Real.exp (-η * a)) = η⁻¹ :=
    integral_laplaceKernel hη
  have hlinevalue :
      (∫ a : ℝ in Set.Ioi 0,
        a * Real.exp (-η * a)) = 1 / η ^ 2 := by
    simpa using! upper_laplace_monomial_integral hη 1
  have hconstvalue :
      (∫ a : ℝ in Set.Ioi 0,
        (ℓ / 2) * Real.exp (-η * a)) =
          (ℓ / 2) * η⁻¹ := by
    rw [integral_const_mul, hzerovalue]
  have hmajorvalue :
      (∫ a : ℝ in Set.Ioi 0,
        (a + ℓ / 2) * Real.exp (-η * a)) =
          1 / η ^ 2 + (ℓ / 2) * η⁻¹ := by
    calc
      (∫ a : ℝ in Set.Ioi 0,
        (a + ℓ / 2) * Real.exp (-η * a)) =
          ∫ a : ℝ in Set.Ioi 0,
            (a * Real.exp (-η * a) +
              (ℓ / 2) * Real.exp (-η * a)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro a ha
              ring
      _ = (∫ a : ℝ in Set.Ioi 0,
            a * Real.exp (-η * a)) +
          ∫ a : ℝ in Set.Ioi 0,
            (ℓ / 2) * Real.exp (-η * a) :=
        integral_add hline hconst
      _ = 1 / η ^ 2 + (ℓ / 2) * η⁻¹ := by
        rw [hlinevalue, hconstvalue]
  have hℓinv : 0 ≤ ℓ⁻¹ := (inv_pos.mpr hℓ).le
  unfold upperGammaVariance
  constructor
  · calc
      1 / (2 * η) =
          ℓ⁻¹ * ((ℓ / 2) * η⁻¹) := by
            field_simp [hℓ.ne', hη.ne']
      _ = ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            (ℓ / 2) * Real.exp (-η * a)) := by
            rw [hconstvalue]
      _ ≤ ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            a ^ 2 * upperGammaMeasureDensity ℓ η a) :=
        mul_le_mul_of_nonneg_left hlowerIntegral hℓinv
  · calc
      ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            a ^ 2 * upperGammaMeasureDensity ℓ η a) ≤
        ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            (a + ℓ / 2) * Real.exp (-η * a)) :=
        mul_le_mul_of_nonneg_left hupperIntegral hℓinv
      _ = ℓ⁻¹ *
          (1 / η ^ 2 + (ℓ / 2) * η⁻¹) := by
            rw [hmajorvalue]
      _ = 1 / (2 * η) + 1 / (ℓ * η ^ 2) := by
            field_simp [hℓ.ne', hη.ne']; ring
end CohnElkies
