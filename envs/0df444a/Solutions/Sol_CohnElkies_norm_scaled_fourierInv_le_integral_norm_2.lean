-- Prove2me | solution 2 for CohnElkies.norm_scaled_fourierInv_le_integral_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:33:53.487625+00:00
-- url     : https://prove2.me/submissions/6d16219c-cdc0-4dc8-9852-2c34cf0a3863

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


theorem solution (Z : ℝ → ℂ) (v : ℝ) :
    ‖((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v)‖ ≤
      (2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖ := by
  rw [Real.fourierInv_eq]
  have hp : (0:ℝ) < 2 * Real.pi := by positivity
  calc ‖∫ ξ : ℝ, 𝐞 (inner ℝ ξ v) • Z (2 * Real.pi * ξ)‖
      ≤ ∫ ξ : ℝ, ‖𝐞 (inner ℝ ξ v) • Z (2 * Real.pi * ξ)‖ := norm_integral_le_integral_norm _
    _ = ∫ ξ : ℝ, ‖Z (2 * Real.pi * ξ)‖ := by
        congr 1; funext ξ; rw [Circle.norm_smul]
    _ = (2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖ := by
        rw [Measure.integral_comp_mul_left (fun s => ‖Z s‖) (2 * Real.pi), smul_eq_mul,
          abs_of_pos (inv_pos.2 hp)]

