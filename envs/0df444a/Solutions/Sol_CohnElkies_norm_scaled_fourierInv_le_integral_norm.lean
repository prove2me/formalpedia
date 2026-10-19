-- Prove2me | solution 1 for CohnElkies.norm_scaled_fourierInv_le_integral_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/a6b4aa8d-eda1-4766-a1d6-02d84a6bb615

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_norm_fourierInv_le_integral_norm

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution (Z : ℝ → ℂ) (v : ℝ) :
    ‖((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v)‖ ≤
      (2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖ := by
  calc
    ‖((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v)‖ ≤
        ∫ ξ : ℝ, ‖Z (2 * Real.pi * ξ)‖ :=
      norm_fourierInv_le_integral_norm
        (fun ξ : ℝ => Z (2 * Real.pi * ξ)) v
    _ = (2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖ := by
      rw [Measure.integral_comp_mul_left
        (fun s : ℝ => ‖Z s‖) (2 * Real.pi)]
      change |(2 * Real.pi)⁻¹| * (∫ s : ℝ, ‖Z s‖) =
        (2 * Real.pi)⁻¹ * (∫ s : ℝ, ‖Z s‖)
      rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
end CohnElkies
