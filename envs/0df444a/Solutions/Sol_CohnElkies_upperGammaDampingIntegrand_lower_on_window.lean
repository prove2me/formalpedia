-- Prove2me | solution 1 for CohnElkies.upperGammaDampingIntegrand_lower_on_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/1d9371cb-89db-4a96-adcd-95cbc3e74267

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaVarianceDensity_pointwise_bounds
import Theorems.Thm_CohnElkies_upperGammaMeasureDensity_pos
import Theorems.Thm_CohnElkies_upper_one_sub_cos_quadratic_lower

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
    {ℓ η T a : ℝ}
    (hℓ : 0 < ℓ) (hη : 0 < η)
    (ha : 0 < a)
    (haη : a ≤ η⁻¹)
    (haT : a ≤ |T|⁻¹)
    (hT : T ≠ 0) :
    (ℓ / (8 * Real.exp 1)) * T ^ 2 ≤
      upperGammaDampingIntegrand ℓ η T a := by
  have hTa : |a * T| ≤ 1 := by
    rw [abs_mul, abs_of_pos ha]
    calc
      a * |T| ≤ |T|⁻¹ * |T| :=
        mul_le_mul_of_nonneg_right haT
          (abs_nonneg T)
      _ = 1 := inv_mul_cancel₀ (abs_ne_zero.mpr hT)
  have heta : η * a ≤ 1 := by
    calc
      η * a ≤ η * η⁻¹ :=
        mul_le_mul_of_nonneg_left haη hη.le
      _ = 1 := mul_inv_cancel₀ hη.ne'
  have hexp : (Real.exp 1)⁻¹ ≤
      Real.exp (-η * a) := by
    rw [← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  have hvariance :=
    (upperGammaVarianceDensity_pointwise_bounds
      (η := η) hℓ ha).1
  have hcos := upper_one_sub_cos_quadratic_lower hTa
  have hdensity := upperGammaMeasureDensity_pos
    (η := η) hℓ ha
  have hquarter : 0 ≤ T ^ 2 / 4 := by positivity
  calc
    (ℓ / (8 * Real.exp 1)) * T ^ 2 =
        (T ^ 2 / 4) *
          ((ℓ / 2) * (Real.exp 1)⁻¹) := by
      field_simp [(Real.exp_pos 1).ne']
      ring
    _ ≤ (T ^ 2 / 4) *
          ((ℓ / 2) * Real.exp (-η * a)) := by
      gcongr
    _ ≤ (T ^ 2 / 4) *
          (a ^ 2 * upperGammaMeasureDensity ℓ η a) :=
      mul_le_mul_of_nonneg_left hvariance hquarter
    _ = ((a * T) ^ 2 / 4) *
          upperGammaMeasureDensity ℓ η a := by
      ring
    _ ≤ (1 - Real.cos (a * T)) *
          upperGammaMeasureDensity ℓ η a :=
      mul_le_mul_of_nonneg_right hcos hdensity.le
    _ = upperGammaDampingIntegrand ℓ η T a := rfl
end CohnElkies
