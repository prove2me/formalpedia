-- Prove2me | solution 2 for CohnElkies.stripPoisson_integral_changeVariables
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:09:02.338753+00:00
-- url     : https://prove2.me/submissions/b61adda7-2506-46ad-8502-aacdf4e55750

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
    {ℓ : ℝ} (hℓ : 0 < ℓ) (σ s : ℝ) (h : ℝ → ℝ) :
    (∫ y : ℝ,
      stripPoissonKernel σ ((s - y) / ℓ) / ℓ * h y) =
      ∫ T : ℝ, stripPoissonKernel σ T * h (s - ℓ * T) := by
  let G : ℝ → ℝ := fun y => stripPoissonKernel σ ((s - y) / ℓ) / ℓ * h y
  have h1 : ∀ T : ℝ, stripPoissonKernel σ T * h (s - ℓ * T) = ℓ * G (s - ℓ * T) := by
    intro T
    simp only [G]
    rw [sub_sub_cancel, mul_div_cancel_left₀ T hℓ.ne']
    field_simp
  have h2 : (∫ T : ℝ, G (s - ℓ * T)) = ℓ⁻¹ * ∫ y, G y := by
    have := Measure.integral_comp_mul_left (fun x => G (s - x)) ℓ
    rw [this, integral_sub_left_eq_self, abs_of_pos (inv_pos.mpr hℓ), smul_eq_mul]
  have h3 : (∫ T : ℝ, stripPoissonKernel σ T * h (s - ℓ * T)) = ∫ T : ℝ, ℓ * G (s - ℓ * T) := by
    congr 1; funext T; exact h1 T
  rw [h3, integral_const_mul, h2, ← mul_assoc, mul_inv_cancel₀ hℓ.ne', one_mul]

