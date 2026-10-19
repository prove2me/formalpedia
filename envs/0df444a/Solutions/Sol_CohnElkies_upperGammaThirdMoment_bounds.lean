-- Prove2me | solution 1 for CohnElkies.upperGammaThirdMoment_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/2d4a425e-9152-400b-a1f1-a58aa2f6b843

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upper_laplace_monomial_integrable
import Theorems.Thm_CohnElkies_upper_laplace_monomial_integral
import Theorems.Thm_CohnElkies_upperGammaThirdMomentDensity_pointwise_bounds
import Theorems.Thm_CohnElkies_upperGammaThirdMomentDensity_integrable

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
    1 / (2 * η ^ 2) ≤ upperGammaThirdMoment ℓ η ∧
      upperGammaThirdMoment ℓ η ≤
        1 / (2 * η ^ 2) + 2 / (ℓ * η ^ 3) := by
  have hline : IntegrableOn
      (fun a : ℝ => a * Real.exp (-η * a))
      (Set.Ioi 0) := by
    simpa using! upper_laplace_monomial_integrable hη 1
  have hquadratic : IntegrableOn
      (fun a : ℝ => a ^ 2 * Real.exp (-η * a))
      (Set.Ioi 0) :=
    upper_laplace_monomial_integrable hη 2
  have hconst : IntegrableOn
      (fun a : ℝ => (ℓ / 2) * a * Real.exp (-η * a))
      (Set.Ioi 0) := by
    have h : IntegrableOn
        (fun a : ℝ =>
          (ℓ / 2) * (a * Real.exp (-η * a)))
        (Set.Ioi 0) :=
      hline.const_mul (ℓ / 2)
    apply h.congr_fun _ measurableSet_Ioi
    intro a ha
    change (ℓ / 2) *
      (a * Real.exp (-η * a)) =
        (ℓ / 2) * a * Real.exp (-η * a)
    ring
  have hactual := upperGammaThirdMomentDensity_integrable hℓ hη
  have hmajor : IntegrableOn
      (fun a : ℝ =>
        (a ^ 2 + (ℓ / 2) * a) * Real.exp (-η * a))
      (Set.Ioi 0) := by
    apply (hquadratic.add hconst).congr_fun _ measurableSet_Ioi
    intro a ha
    change a ^ 2 * Real.exp (-η * a) +
      (ℓ / 2) * a * Real.exp (-η * a) =
        (a ^ 2 + (ℓ / 2) * a) * Real.exp (-η * a)
    ring
  have hlowerIntegral :
      (∫ a : ℝ in Set.Ioi 0,
        (ℓ / 2) * a * Real.exp (-η * a)) ≤
        ∫ a : ℝ in Set.Ioi 0,
          a ^ 3 * upperGammaMeasureDensity ℓ η a := by
    apply integral_mono_ae hconst hactual
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    exact (upperGammaThirdMomentDensity_pointwise_bounds
      (η := η) hℓ ha).1
  have hupperIntegral :
      (∫ a : ℝ in Set.Ioi 0,
        a ^ 3 * upperGammaMeasureDensity ℓ η a) ≤
        ∫ a : ℝ in Set.Ioi 0,
          (a ^ 2 + (ℓ / 2) * a) *
            Real.exp (-η * a) := by
    apply integral_mono_ae hactual hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    exact (upperGammaThirdMomentDensity_pointwise_bounds
      (η := η) hℓ ha).2
  have hlinevalue :
      (∫ a : ℝ in Set.Ioi 0,
        a * Real.exp (-η * a)) = 1 / η ^ 2 := by
    simpa using! upper_laplace_monomial_integral hη 1
  have hquadraticvalue :
      (∫ a : ℝ in Set.Ioi 0,
        a ^ 2 * Real.exp (-η * a)) = 2 / η ^ 3 := by
    simpa using! upper_laplace_monomial_integral hη 2
  have hconstvalue :
      (∫ a : ℝ in Set.Ioi 0,
        (ℓ / 2) * a * Real.exp (-η * a)) =
          (ℓ / 2) * (1 / η ^ 2) := by
    calc
      (∫ a : ℝ in Set.Ioi 0,
        (ℓ / 2) * a * Real.exp (-η * a)) =
          ∫ a : ℝ in Set.Ioi 0,
            (ℓ / 2) *
              (a * Real.exp (-η * a)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro a ha
              ring
      _ = (ℓ / 2) *
          (∫ a : ℝ in Set.Ioi 0,
            a * Real.exp (-η * a)) := by
        rw [integral_const_mul]
      _ = (ℓ / 2) * (1 / η ^ 2) := by
        rw [hlinevalue]
  have hmajorvalue :
      (∫ a : ℝ in Set.Ioi 0,
        (a ^ 2 + (ℓ / 2) * a) * Real.exp (-η * a)) =
          2 / η ^ 3 + (ℓ / 2) * (1 / η ^ 2) := by
    calc
      (∫ a : ℝ in Set.Ioi 0,
        (a ^ 2 + (ℓ / 2) * a) * Real.exp (-η * a)) =
          ∫ a : ℝ in Set.Ioi 0,
            (a ^ 2 * Real.exp (-η * a) +
              (ℓ / 2) * a * Real.exp (-η * a)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro a ha
              ring
      _ = (∫ a : ℝ in Set.Ioi 0,
            a ^ 2 * Real.exp (-η * a)) +
          ∫ a : ℝ in Set.Ioi 0,
            (ℓ / 2) * a * Real.exp (-η * a) :=
        integral_add hquadratic hconst
      _ = 2 / η ^ 3 + (ℓ / 2) * (1 / η ^ 2) := by
        rw [hquadraticvalue, hconstvalue]
  have hℓinv : 0 ≤ ℓ⁻¹ := (inv_pos.mpr hℓ).le
  unfold upperGammaThirdMoment
  constructor
  · calc
      1 / (2 * η ^ 2) =
          ℓ⁻¹ * ((ℓ / 2) * (1 / η ^ 2)) := by
            field_simp [hℓ.ne', hη.ne']
      _ = ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            (ℓ / 2) * a * Real.exp (-η * a)) := by
            rw [hconstvalue]
      _ ≤ ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            a ^ 3 * upperGammaMeasureDensity ℓ η a) :=
        mul_le_mul_of_nonneg_left hlowerIntegral hℓinv
  · calc
      ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            a ^ 3 * upperGammaMeasureDensity ℓ η a) ≤
        ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            (a ^ 2 + (ℓ / 2) * a) *
              Real.exp (-η * a)) :=
        mul_le_mul_of_nonneg_left hupperIntegral hℓinv
      _ = ℓ⁻¹ *
          (2 / η ^ 3 + (ℓ / 2) * (1 / η ^ 2)) := by
            rw [hmajorvalue]
      _ = 1 / (2 * η ^ 2) + 2 / (ℓ * η ^ 3) := by
            field_simp [hℓ.ne', hη.ne']; ring
end CohnElkies
