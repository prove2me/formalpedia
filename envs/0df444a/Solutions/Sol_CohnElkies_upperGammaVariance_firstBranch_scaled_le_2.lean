-- Prove2me | solution 2 for CohnElkies.upperGammaVariance_firstBranch_scaled_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:42:54.817718+00:00
-- url     : https://prove2.me/submissions/a54cc831-be36-47e7-929a-8b639c0fe27d

import Mathlib
import Definitions.Def_SpherePacking
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
    η * upperGammaVariance ℓ η ≤ (3 / 2 : ℝ) := by
  have hbounds : 1 / (2 * η) ≤ upperGammaVariance ℓ η ∧ upperGammaVariance ℓ η ≤ 1 / (2 * η) + 1 / (ℓ * η ^ 2) := by
    have hmain : ∀ a : ℝ, 0 < a →
        (ℓ / 2) * Real.exp (-η * a) ≤ a ^ 2 * upperGammaMeasureDensity ℓ η a ∧
        a ^ 2 * upperGammaMeasureDensity ℓ η a ≤
          (ℓ / 2) * Real.exp (-η * a) + a * Real.exp (-η * a) := by
      intro a ha'
      unfold upperGammaMeasureDensity
      have hx : 0 < 2 * a / ℓ := by positivity
      have hE : Real.exp (-(2 * a / ℓ)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have hden : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by linarith
      have hup : 1 - Real.exp (-(2 * a / ℓ)) ≤ 2 * a / ℓ := by
        have := Real.add_one_le_exp (-(2 * a / ℓ)); linarith
      have hbound : (2 * a / ℓ) / (1 + 2 * a / ℓ) ≤ 1 - Real.exp (-(2 * a / ℓ)) := by
        have h1 := Real.add_one_le_exp (2 * a / ℓ)
        have h2 : Real.exp (-(2 * a / ℓ)) = (Real.exp (2 * a / ℓ))⁻¹ := Real.exp_neg _
        rw [h2, div_le_iff₀ (by positivity)]
        have h3 := Real.exp_pos (2 * a / ℓ)
        have h4 : (Real.exp (2 * a / ℓ))⁻¹ * Real.exp (2 * a / ℓ) = 1 := inv_mul_cancel₀ h3.ne'
        nlinarith [mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr h3.le)]
      have he := Real.exp_pos (-η * a)
      have heq : a ^ 2 * (Real.exp (-η * a) / (a * (1 - Real.exp (-(2 * a / ℓ))))) =
          Real.exp (-η * a) * (a / (1 - Real.exp (-(2 * a / ℓ)))) := by
        field_simp
      rw [heq]
      constructor
      · have key : ℓ / 2 ≤ a / (1 - Real.exp (-(2 * a / ℓ))) := by
          rw [le_div_iff₀ hden]
          have : ℓ / 2 * (2 * a / ℓ) = a := by field_simp
          nlinarith
        nlinarith
      · have key : a / (1 - Real.exp (-(2 * a / ℓ))) ≤ ℓ / 2 + a := by
          rw [div_le_iff₀ hden]
          have : (ℓ / 2 + a) * ((2 * a / ℓ) / (1 + 2 * a / ℓ)) = a := by field_simp <;> ring
          nlinarith [mul_le_mul_of_nonneg_left hbound (by positivity : (0:ℝ) ≤ ℓ / 2 + a)]
        nlinarith
    have hI1 : IntegrableOn (fun a : ℝ => (ℓ / 2) * Real.exp (-η * a)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hη).const_mul _
    have hI2' : IntegrableOn (fun a : ℝ => a * Real.exp (-η * a)) (Ioi 0) := by
      have := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := η) (by norm_num) one_pos hη)
      refine this.congr_fun (fun a ha => ?_) measurableSet_Ioi
      simp only [Real.rpow_one]
    have hI2 : IntegrableOn (fun a : ℝ => (ℓ / 2) * Real.exp (-η * a) + a * Real.exp (-η * a)) (Ioi 0) :=
      hI1.add hI2'
    have hmeas : Measurable (fun a : ℝ => a ^ 2 * upperGammaMeasureDensity ℓ η a) := by
      unfold upperGammaMeasureDensity; fun_prop
    have hf : IntegrableOn (fun a : ℝ => a ^ 2 * upperGammaMeasureDensity ℓ η a) (Ioi 0) := by
      refine Integrable.mono' hI2 hmeas.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      have h := hmain a ha
      have he := Real.exp_pos (-η * a)
      rw [Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
      exact h.2
    have hJ1 : (∫ a : ℝ in Ioi 0, (ℓ / 2) * Real.exp (-η * a)) = ℓ / (2 * η) := by
      rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith : -η < 0) 0]
      simp
      field_simp
    have hJ2 : (∫ a : ℝ in Ioi 0, a * Real.exp (-η * a)) = 1 / η ^ 2 := by
      have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) two_pos hη
      rw [Real.Gamma_two, mul_one] at h
      have hc : (∫ t : ℝ in Ioi 0, t ^ ((2:ℝ) - 1) * Real.exp (-(η * t))) =
          ∫ a : ℝ in Ioi 0, a * Real.exp (-η * a) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp only
        norm_num
      rw [← hc, h, Real.rpow_two]
      field_simp
    have hlow := setIntegral_mono_on hI1 hf measurableSet_Ioi (fun a ha => (hmain a ha).1)
    have hhigh := setIntegral_mono_on hf hI2 measurableSet_Ioi (fun a ha => (hmain a ha).2)
    rw [integral_add hI1 hI2', hJ1, hJ2] at hhigh
    rw [hJ1] at hlow
    unfold upperGammaVariance
    have hℓi : 0 < ℓ⁻¹ := inv_pos.mpr hℓ
    constructor
    · calc 1 / (2 * η) = ℓ⁻¹ * (ℓ / (2 * η)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow hℓi.le
    · calc _ ≤ ℓ⁻¹ * (ℓ / (2 * η) + 1 / η ^ 2) := mul_le_mul_of_nonneg_left hhigh hℓi.le
        _ = 1 / (2 * η) + 1 / (ℓ * η ^ 2) := by field_simp
  have h2 := hbounds.2
  have h3 : η * (1 / (2 * η) + 1 / (ℓ * η ^ 2)) = 1 / 2 + 1 / (ℓ * η) := by field_simp
  have h4 : 1 / (ℓ * η) ≤ 1 := by rw [div_le_one (by positivity)]; exact hscale
  nlinarith [mul_le_mul_of_nonneg_left h2 hη.le]

