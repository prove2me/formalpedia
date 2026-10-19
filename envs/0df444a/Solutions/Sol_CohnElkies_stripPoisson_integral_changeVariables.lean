-- Prove2me | solution 1 for CohnElkies.stripPoisson_integral_changeVariables
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/ff7428d3-3ba7-414e-a6f2-0e17315000ff

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
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) (σ s : ℝ) (h : ℝ → ℝ) :
    (∫ y : ℝ,
      stripPoissonKernel σ ((s - y) / ℓ) / ℓ * h y) =
      ∫ T : ℝ, stripPoissonKernel σ T * h (s - ℓ * T) := by
  let G : ℝ → ℝ :=
    fun y => stripPoissonKernel σ ((s - y) / ℓ) / ℓ * h y
  have hscale :
      (∫ T : ℝ, G (s - ℓ * T)) =
        ℓ⁻¹ * ∫ y : ℝ, G y := by
    have hraw := Measure.integral_comp_mul_left
      (fun u : ℝ => G (s + u)) (-ℓ)
    rw [integral_add_left_eq_self G s] at hraw
    simpa [sub_eq_add_neg, neg_mul, inv_neg, abs_neg,
      abs_of_pos (inv_pos.mpr hℓ), smul_eq_mul] using! hraw
  have hrewrite :
      (∫ T : ℝ, G (s - ℓ * T)) =
        ℓ⁻¹ *
          ∫ T : ℝ, stripPoissonKernel σ T * h (s - ℓ * T) := by
    calc
      (∫ T : ℝ, G (s - ℓ * T)) =
          ∫ T : ℝ,
            ℓ⁻¹ *
              (stripPoissonKernel σ T * h (s - ℓ * T)) := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall (fun T => ?_)
        have hargument : (s - (s - ℓ * T)) / ℓ = T := by
          field_simp [hℓ.ne']
          ring
        try dsimp [G]
        rw [hargument]
        ring
      _ = ℓ⁻¹ *
          ∫ T : ℝ, stripPoissonKernel σ T * h (s - ℓ * T) := by
        rw [integral_const_mul]
  change (∫ y : ℝ, G y) =
    ∫ T : ℝ, stripPoissonKernel σ T * h (s - ℓ * T)
  exact mul_left_cancel₀ (inv_ne_zero hℓ.ne')
    (hscale.symm.trans hrewrite)
end CohnElkies
