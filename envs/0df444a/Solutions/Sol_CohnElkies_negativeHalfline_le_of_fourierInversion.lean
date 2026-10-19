-- Prove2me | solution 1 for CohnElkies.negativeHalfline_le_of_fourierInversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/e6145619-7aaf-4145-9b05-6a1543a189d6

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedProfile_negativeHalfline_le_of_exp_majorant
import Theorems.Thm_CohnElkies_norm_scaled_fourierInv_le_integral_norm

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    {a : ℝ} (ha : 0 < a) (Z : ℝ → ℂ)
    (hinversion : ∀ v : ℝ,
      (φ v : ℂ) = (Real.exp (a * v) : ℂ) *
        ((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v)) :
    (∫ v in Iic (0 : ℝ), |φ v|) ≤
      ((2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖) / a := by
  apply normalizedProfile_negativeHalfline_le_of_exp_majorant hφ ha
  intro v _
  calc
    |φ v| = ‖(φ v : ℂ)‖ := by simp
    _ = ‖(Real.exp (a * v) : ℂ) *
        ((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v)‖ := by
      rw [hinversion v]
    _ = Real.exp (a * v) *
        ‖((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v)‖ := by
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
    _ ≤ Real.exp (a * v) *
        ((2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_scaled_fourierInv_le_integral_norm Z v)
        (Real.exp_pos _).le
    _ = ((2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖) *
        Real.exp (a * v) := by ring
end CohnElkies
