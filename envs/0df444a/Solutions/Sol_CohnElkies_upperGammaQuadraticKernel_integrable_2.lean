-- Prove2me | solution 2 for CohnElkies.upperGammaQuadraticKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:33:50.424534+00:00
-- url     : https://prove2.me/submissions/625cf222-bc2b-4285-a976-7cde410a2631

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    IntegrableOn (upperGammaQuadraticKernel ℓ η T)
      (Ioi 0) := by
  have hmeas : Measurable (upperGammaQuadraticKernel ℓ η T) := by
    unfold upperGammaQuadraticKernel upperGammaMeasureDensity; fun_prop
  have hg : IntegrableOn (fun a : ℝ => T ^ 2 / 2 * ((ℓ / 2) * Real.exp (-η * a) + a * Real.exp (-η * a))) (Ioi 0) := by
    apply Integrable.const_mul
    apply Integrable.add
    · exact (exp_neg_integrableOn_Ioi 0 hη).const_mul _
    · have := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := η) (by norm_num) one_pos hη)
      refine this.congr_fun (fun a ha => ?_) measurableSet_Ioi
      simp only [Real.rpow_one]
  refine Integrable.mono' hg hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  have ha' : (0:ℝ) < a := ha
  unfold upperGammaQuadraticKernel upperGammaMeasureDensity
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hx : 0 < 2 * a / ℓ := by positivity
  have hE : Real.exp (-(2 * a / ℓ)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by linarith
  -- 1 - e^{-x} ≥ x/(1+x)
  have hbound : (2 * a / ℓ) / (1 + 2 * a / ℓ) ≤ 1 - Real.exp (-(2 * a / ℓ)) := by
    have h1 := Real.add_one_le_exp (2 * a / ℓ)
    have h2 : Real.exp (-(2 * a / ℓ)) = (Real.exp (2 * a / ℓ))⁻¹ := Real.exp_neg _
    rw [h2, div_le_iff₀ (by positivity)]
    have h3 := Real.exp_pos (2 * a / ℓ)
    have h4 : (Real.exp (2 * a / ℓ))⁻¹ * Real.exp (2 * a / ℓ) = 1 := inv_mul_cancel₀ h3.ne'
    nlinarith [mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr h3.le)]
  have he := Real.exp_pos (-η * a)
  rw [abs_of_nonneg (by positivity)]
  have key : a / (1 - Real.exp (-(2 * a / ℓ))) ≤ ℓ / 2 + a := by
    rw [div_le_iff₀ hden]
    have : (ℓ / 2 + a) * ((2 * a / ℓ) / (1 + 2 * a / ℓ)) = a := by field_simp <;> ring
    nlinarith [mul_le_mul_of_nonneg_left hbound (by positivity : (0:ℝ) ≤ ℓ / 2 + a)]
  calc (a * T) ^ 2 / 2 * (Real.exp (-η * a) / (a * (1 - Real.exp (-(2 * a / ℓ)))))
      = T ^ 2 / 2 * Real.exp (-η * a) * (a / (1 - Real.exp (-(2 * a / ℓ)))) := by
        field_simp
    _ ≤ T ^ 2 / 2 * Real.exp (-η * a) * (ℓ / 2 + a) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = T ^ 2 / 2 * ((ℓ / 2) * Real.exp (-η * a) + a * Real.exp (-η * a)) := by ring

