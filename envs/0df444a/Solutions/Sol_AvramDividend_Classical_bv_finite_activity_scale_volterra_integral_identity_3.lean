-- Prove2me | solution 3 for AvramDividend.Classical.bv_finite_activity_scale_volterra_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:18:47.076291+00:00
-- url     : https://prove2.me/submissions/1d32594e-784d-43cb-b83b-37081b8f7ffd

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_volterra_laplace_family
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_volterra_rhs_continuous
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq_signed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ x : ℝ, 0 < x →
      X.drift * W x =
        1 + (q + (X.ν (Iio (0 : ℝ))).toReal) *
          (∫ z in (0 : ℝ)..x, W z) -
          ∫ z in (0 : ℝ)..x,
            (∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν) := by
  obtain ⟨b, hLap⟩ :=
    bv_finite_activity_volterra_laplace_family X hX q hq W hW hBV hFinite
  obtain ⟨hContLeft, hContRight⟩ :=
    bv_finite_activity_volterra_rhs_continuous X hX q hq W hW hBV hFinite
  exact continuousOn_Ioi_eq_of_laplace_eq_signed
    (fun x : ℝ => X.drift * W x)
    (fun x : ℝ =>
      1 + (q + (X.ν (Iio (0 : ℝ))).toReal) *
        (∫ z in (0 : ℝ)..x, W z) -
        ∫ z in (0 : ℝ)..x,
          (∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν))
    b hContLeft hContRight (by
      intro θ hθ
      simpa only [neg_mul, mul_assoc] using hLap θ hθ)
