-- Prove2me | solution 2 for CohnElkies.upperGammaThirdMoment_firstBranch_scaled_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:40:11.043766+00:00
-- url     : https://prove2.me/submissions/35d88456-62ac-47db-a7ad-e440c1120d87

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upper_laplace_monomial_integral
import Theorems.Thm_CohnElkies_upperGammaThirdMomentDensity_integrable
import Theorems.Thm_CohnElkies_upperGammaVariance_bounds
import Theorems.Thm_CohnElkies_upperGammaVarianceDensity_pointwise_bounds
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (hscale : 1 ≤ ℓ * η) :
    η ^ 2 * upperGammaThirdMoment ℓ η ≤ (5 / 2 : ℝ) := by
  have hℓ0 : 0 < ℓ := hℓ
  have hη0 : 0 < η := hη
  have hI : ∀ k : ℕ, IntegrableOn (fun a : ℝ => a ^ k * Real.exp (-η * a)) (Set.Ioi 0) := by
    intro k
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (k : ℝ)) (p := 1) (b := η)
      (by have := k.cast_nonneg (α := ℝ); linarith) one_pos hη0
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp [Real.rpow_natCast]
  have hmaj : IntegrableOn (fun a : ℝ => a ^ 2 * Real.exp (-η * a) + ℓ / 2 * (a ^ 1 * Real.exp (-η * a)))
      (Set.Ioi 0) := (hI 2).add ((hI 1).const_mul _)
  have hle : (∫ a : ℝ in Set.Ioi 0, a ^ 3 * upperGammaMeasureDensity ℓ η a) ≤
      ∫ a : ℝ in Set.Ioi 0, a ^ 2 * Real.exp (-η * a) + ℓ / 2 * (a ^ 1 * Real.exp (-η * a)) := by
    refine setIntegral_mono_on (CohnElkies.upperGammaThirdMomentDensity_integrable hℓ0 hη0) hmaj
      measurableSet_Ioi (fun a ha => ?_)
    have ha0 : (0:ℝ) < a := ha
    have hb := (CohnElkies.upperGammaVarianceDensity_pointwise_bounds (η := η) hℓ0 ha0).2
    calc a ^ 3 * upperGammaMeasureDensity ℓ η a = a * (a ^ 2 * upperGammaMeasureDensity ℓ η a) := by ring
      _ ≤ a * ((a + ℓ / 2) * Real.exp (-η * a)) := mul_le_mul_of_nonneg_left hb ha0.le
      _ = _ := by ring
  have hval : (∫ a : ℝ in Set.Ioi 0, a ^ 2 * Real.exp (-η * a) + ℓ / 2 * (a ^ 1 * Real.exp (-η * a))) =
      2 / η ^ 3 + ℓ / 2 * (1 / η ^ 2) := by
    rw [MeasureTheory.integral_add (hI 2) ((hI 1).const_mul _), MeasureTheory.integral_const_mul,
      CohnElkies.upper_laplace_monomial_integral hη0 2, CohnElkies.upper_laplace_monomial_integral hη0 1]
    norm_num
  unfold upperGammaThirdMoment
  rw [hval] at hle
  have hinv : 0 < ℓ⁻¹ := inv_pos.mpr hℓ0
  have h1 : ℓ⁻¹ * (∫ a : ℝ in Set.Ioi 0, a ^ 3 * upperGammaMeasureDensity ℓ η a) ≤
      ℓ⁻¹ * (2 / η ^ 3 + ℓ / 2 * (1 / η ^ 2)) := mul_le_mul_of_nonneg_left hle hinv.le
  have h2 : η ^ 2 * (ℓ⁻¹ * (2 / η ^ 3 + ℓ / 2 * (1 / η ^ 2))) = 2 / (ℓ * η) + 1 / 2 := by
    field_simp
  have h3 : 2 / (ℓ * η) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ η ^ 2)
  linarith

