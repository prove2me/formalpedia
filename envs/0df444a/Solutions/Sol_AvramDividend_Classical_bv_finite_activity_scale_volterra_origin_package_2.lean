-- Prove2me | solution 2 for AvramDividend.Classical.bv_finite_activity_scale_volterra_origin_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:39:23.424647+00:00
-- url     : https://prove2.me/submissions/07637091-bbc3-4bea-a9bc-b31d43c0bad7

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_scale_origin_eq_inv_drift
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_derivative_jump_convolution_identity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- The BV scale-origin identity and finite-jump convolution supply the
    Volterra remainder, conditional on its pointwise derivative equation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    W 0 = 1 / X.drift ∧
      ∃ G : ℝ → ℝ,
        ContinuousWithinAt W (Ioi (0 : ℝ)) 0 ∧
        Tendsto G (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) ∧
        (∀ x : ℝ, 0 < x →
          deriv W x =
            ((q + (X.ν (Iio (0 : ℝ))).toReal) / X.drift) * W x -
              G x / X.drift) := by
  have hd : X.drift ≠ 0 :=
    ne_of_gt (bv_standing_drift_pos X hX hBV).1
  have hcont : ContinuousWithinAt W (Ioi (0 : ℝ)) 0 :=
    (hW.2.2.1.continuousWithinAt (by simp)).mono
      (by intro y hy; exact le_of_lt (mem_Ioi.mp hy))
  refine ⟨bv_scale_origin_eq_inv_drift X hX q hq W hW hBV, ?_⟩
  refine ⟨(fun x : ℝ => ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν),
    hcont, ?_, ?_⟩
  · exact bv_finite_activity_scale_jump_convolution_tendsto_zero
      X hX q hq W hW hBV hFinite
  · intro x hx
    have hder := bv_finite_activity_scale_derivative_jump_convolution_identity
      X hX q hq W hW hBV hFinite x hx
    calc
      deriv W x =
          ((q + (X.ν (Iio (0 : ℝ))).toReal) * W x -
            ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν) / X.drift := by
              apply (eq_div_iff hd).2
              simpa only [mul_comm] using hder
      _ = ((q + (X.ν (Iio (0 : ℝ))).toReal) / X.drift) * W x -
          (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν) / X.drift := by ring
