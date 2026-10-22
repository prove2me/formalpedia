-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_laplace_real_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:55:28.125772+00:00
-- url     : https://prove2.me/submissions/7bb9f0f5-6c50-41a7-a603-ad2d17cb9e94

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_esscher_laplace_transform
import Theorems.Thm_AvramDividend_Classical_gaussian_shifted_compensator_real_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_compensated_jump_pos_linear

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- The finite ENNReal double-tail Laplace transform equals the actual real jump integral. -/
theorem solution (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 < θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    θ ^ 2 *
      (∫⁻ t : ℝ, ∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ ∂volume).toReal =
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-φ * z) *
          (Real.exp (-θ * z) - 1 + θ * z) ∂μ) := by
  let ν : Measure ℝ := μ.restrict (Ioi (0 : ℝ))
  let C : ℝ → ℝ := fun z =>
    Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z)
  have hCint : Integrable C ν := by
    change IntegrableOn C (Ioi (0 : ℝ)) μ
    simpa only [C] using
      (gaussian_shifted_compensator_real_integrable μ φ θ
        hφ hθ.le hlevy)
  have hmem : ∀ᵐ z : ℝ ∂ν, z ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem (μ := μ) measurableSet_Ioi
  have hCnn : ∀ᵐ z : ℝ ∂ν, 0 ≤ C z := by
    filter_upwards [hmem] with z hz
    change 0 < z at hz
    change 0 ≤ Real.exp (-φ * z) *
      (Real.exp (-θ * z) - 1 + θ * z)
    exact mul_nonneg (le_of_lt (Real.exp_pos _))
      (gaussian_compensated_jump_pos_linear θ z hθ.le hz.le).1
  have hCeq :
      ENNReal.ofReal (∫ z : ℝ, C z ∂ν) =
        (∫⁻ z : ℝ, ENNReal.ofReal (C z) ∂ν) :=
    ofReal_integral_eq_lintegral_ofReal hCint hCnn
  have hCreal :
      (∫⁻ z : ℝ, ENNReal.ofReal (C z) ∂ν).toReal =
        (∫ z : ℝ, C z ∂ν) := by
    have hcR := congrArg ENNReal.toReal hCeq
    rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hCnn)] at hcR
    exact hcR.symm
  have hTransR :
      θ ^ 2 *
        (∫⁻ t : ℝ, ∫⁻ z : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
              ENNReal.ofReal (Real.exp (-φ * z))
           else 0) ∂μ ∂volume).toReal =
          (∫⁻ z : ℝ, ENNReal.ofReal (C z) ∂ν).toReal := by
    have he := congrArg ENNReal.toReal
      (gaussian_double_tail_esscher_laplace_transform μ φ θ hφ hθ.le)
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sq_nonneg θ)] at he
    simpa only [C, ν] using he
  change θ ^ 2 *
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ ∂volume).toReal = (∫ z : ℝ, C z ∂ν)
  exact hTransR.trans hCreal
