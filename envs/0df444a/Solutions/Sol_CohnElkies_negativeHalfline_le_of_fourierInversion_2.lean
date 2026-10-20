-- Prove2me | solution 2 for CohnElkies.negativeHalfline_le_of_fourierInversion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:58:41.411092+00:00
-- url     : https://prove2.me/submissions/70c89394-d64c-4cfe-9810-ec93d00d24dd

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology


theorem solution
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    {a : ℝ} (ha : 0 < a) (Z : ℝ → ℂ)
    (hinversion : ∀ v : ℝ,
      (φ v : ℂ) = (Real.exp (a * v) : ℂ) *
        ((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v)) :
    (∫ v in Iic (0 : ℝ), |φ v|) ≤
      ((2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖) / a := by
  set K : ℝ := ∫ s : ℝ, ‖Z s‖ with hK
  have hnorm : ∀ v : ℝ, ‖(𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v‖ ≤ (2 * Real.pi)⁻¹ * K := by
    intro v
    rw [Real.fourierInv_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp only [Circle.norm_smul]
    have := MeasureTheory.Measure.integral_comp_mul_left (fun s : ℝ => ‖Z s‖) (2 * Real.pi)
    rw [this, smul_eq_mul, abs_of_pos (by positivity)]
  have hpt : ∀ v : ℝ, |φ v| ≤ Real.exp (a * v) * ((2 * Real.pi)⁻¹ * K) := by
    intro v
    have h := congrArg norm (hinversion v)
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at h
    rw [h]
    exact mul_le_mul_of_nonneg_left (hnorm v) (Real.exp_pos _).le
  calc (∫ v in Iic (0 : ℝ), |φ v|)
      ≤ ∫ v in Iic (0 : ℝ), Real.exp (a * v) * ((2 * Real.pi)⁻¹ * K) := by
        apply MeasureTheory.setIntegral_mono_on hφ.abs.integrableOn
          ((integrableOn_exp_mul_Iic ha 0).mul_const _) measurableSet_Iic
        intro v _; exact hpt v
    _ = ((2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖) / a := by
        rw [MeasureTheory.integral_mul_const, integral_exp_mul_Iic ha 0]
        simp [hK]
        ring

