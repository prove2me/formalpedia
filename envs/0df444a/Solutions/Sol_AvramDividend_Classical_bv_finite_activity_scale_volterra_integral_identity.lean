-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_scale_volterra_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:53:49.79776+00:00
-- url     : https://prove2.me/submissions/9321ae51-9ca5-4bf3-ac1e-8921dd9ae878

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_volterra_laplace_family
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_intervalIntegrable_nonnegative
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_continuous_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_positive_kernel_primitive_contDiff_one
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq_signed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Recover the BV finite-activity renewal identity using Laplace uniqueness. -/
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
  let G : ℝ → ℝ := fun z => ∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν
  have hWcont : ContinuousOn W (Ioi (0 : ℝ)) := by
    intro x hx
    exact (scaleFunction_continuousAt_away_zero X q W hW x
      (ne_of_gt hx)).continuousWithinAt
  have hGclosed : ContinuousOn G (Ici (0 : ℝ)) :=
    bv_finite_activity_scale_jump_convolution_continuous_nonnegative
      X hX q hq W hW hBV hFinite
  have hGcont : ContinuousOn G (Ioi (0 : ℝ)) :=
    hGclosed.mono Ioi_subset_Ici_self
  have hWint : ∀ x : ℝ, 0 < x → IntervalIntegrable W volume 0 x := by
    intro x hx
    exact scaleFunction_intervalIntegrable_nonnegative
      X q W hW 0 x le_rfl hx.le
  have hGint : ∀ x : ℝ, 0 < x → IntervalIntegrable G volume 0 x := by
    intro x hx
    have hIcc : ContinuousOn G (Icc (0 : ℝ) x) := by
      apply hGclosed.mono
      intro z hz
      exact (mem_Icc.mp hz).1
    exact ContinuousOn.intervalIntegrable_of_Icc hx.le hIcc
  have hWprim : ContinuousOn
      (fun x : ℝ => ∫ z in (0 : ℝ)..x, W z) (Ioi (0 : ℝ)) :=
    (causal_positive_kernel_primitive_contDiff_one W hWcont hWint).continuousOn
  have hGprim : ContinuousOn
      (fun x : ℝ => ∫ z in (0 : ℝ)..x, G z) (Ioi (0 : ℝ)) :=
    (causal_positive_kernel_primitive_contDiff_one G hGcont hGint).continuousOn
  have hfcont : ContinuousOn
      (fun x : ℝ => X.drift * W x) (Ioi (0 : ℝ)) :=
    continuousOn_const.mul hWcont
  have hgcont : ContinuousOn
      (fun x : ℝ =>
        1 + (q + (X.ν (Iio (0 : ℝ))).toReal) *
          (∫ z in (0 : ℝ)..x, W z) -
          ∫ z in (0 : ℝ)..x,
            (∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν))
      (Ioi (0 : ℝ)) := by
    change ContinuousOn (fun x : ℝ =>
      1 + (q + (X.ν (Iio (0 : ℝ))).toReal) *
        (∫ z in (0 : ℝ)..x, W z) -
      ∫ z in (0 : ℝ)..x, G z) (Ioi (0 : ℝ))
    exact (continuousOn_const.add (continuousOn_const.mul hWprim)).sub hGprim
  obtain ⟨b, hLap⟩ :=
    bv_finite_activity_volterra_laplace_family X hX q hq W hW hBV hFinite
  exact continuousOn_Ioi_eq_of_laplace_eq_signed
    (fun x : ℝ => X.drift * W x)
    (fun x : ℝ =>
      1 + (q + (X.ν (Iio (0 : ℝ))).toReal) *
        (∫ z in (0 : ℝ)..x, W z) -
      ∫ z in (0 : ℝ)..x,
        (∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν))
    b hfcont hgcont (by
      intro θ hθ
      simpa only [neg_mul, mul_assoc] using hLap θ hθ)
