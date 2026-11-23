-- Prove2me | solution 1 for Formalism.DimensionVariation.gaussianIntegralDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:02.315878+00:00
-- url     : https://prove2.me/submissions/26ae2444-243e-4137-804b-763abf4e2436

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_BlockIntegralOf
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_HeightsoundOf
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GaussCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset MeasureTheory
open scoped ComplexConjugate Real
namespace Formalism.DimensionVariation
private theorem integral_complex_exp_neg_mul_sq_norm {c : ℝ} (hc : 0 < c) :
    ∫ z : ℂ, Real.exp (-(c * ‖z‖ ^ 2)) = π / c := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  calc ∫ z : ℂ, Real.exp (-(c * ‖z‖ ^ 2))
      = ∫ z : ℂ, (fun p : ℝ × ℝ => Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2))
          (Complex.measurableEquivRealProd z) := by
        congr 1
        funext z
        show Real.exp (-(c * ‖z‖ ^ 2)) = Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2)
        rw [← Real.exp_add, hsq]
        congr 1
        ring
    _ = ∫ p : ℝ × ℝ, Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2) := by
        exact Complex.volume_preserving_equiv_real_prod.integral_comp'
          (fun p : ℝ × ℝ => Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2))
    _ = (∫ x : ℝ, Real.exp (-c * x ^ 2)) * ∫ y : ℝ, Real.exp (-c * y ^ 2) :=
        integral_prod_mul (fun x : ℝ => Real.exp (-c * x ^ 2)) (fun y : ℝ => Real.exp (-c * y ^ 2))
    _ = π / c := by
        rw [integral_gaussian]
        exact Real.mul_self_sqrt (div_nonneg Real.pi_pos.le hc.le)
end Formalism.DimensionVariation
end

set_option autoImplicit false
open Finset MeasureTheory
open scoped ComplexConjugate Real
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution : GaussCoord := by
  intro κ hκ b hb
  have hint_r : ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2) = ∏ x, π / b x := by
    calc ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2)
        = ∫ u : κ → ℂ, ∏ x, Real.exp (-(b x * ‖u x‖ ^ 2)) := by
          congr 1
          funext u
          rw [← Finset.sum_neg_distrib, Real.exp_sum]
      _ = ∏ x, ∫ z : ℂ, Real.exp (-(b x * ‖z‖ ^ 2)) := by
          exact MeasureTheory.integral_fintype_prod_volume_eq_prod
            (fun x (z : ℂ) => Real.exp (-(b x * ‖z‖ ^ 2)))
      _ = ∏ x, π / b x :=
          Finset.prod_congr rfl fun x _ => integral_complex_exp_neg_mul_sq_norm (hb x)
  refine ⟨?_, hint_r⟩
  by_contra hni
  have h0 : ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2) = 0 := integral_undef hni
  rw [hint_r] at h0
  exact (Finset.prod_ne_zero_iff.mpr fun x _ => div_ne_zero Real.pi_ne_zero (hb x).ne') h0
end Formalism.DimensionVariation
