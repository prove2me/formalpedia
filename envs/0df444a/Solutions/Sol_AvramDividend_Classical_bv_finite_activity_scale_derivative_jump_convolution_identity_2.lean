-- Prove2me | solution 2 for AvramDividend.Classical.bv_finite_activity_scale_derivative_jump_convolution_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:30:30.145582+00:00
-- url     : https://prove2.me/submissions/fc2d4b38-e81f-453d-89bd-e108b659bdfb

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_volterra_integral_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_intervalIntegrable_nonnegative
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_continuous_nonnegative
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_continuous_positive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set intervalIntegral
open scoped NNReal ENNReal

/-- Differentiate the finite-activity scale Volterra identity at positive reserves. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ x : ℝ, 0 < x →
      X.drift * deriv W x =
        (q + (X.ν (Iio (0 : ℝ))).toReal) * W x -
          ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν := by
  intro x hx
  have hd : X.drift ≠ 0 := ne_of_gt (bv_standing_drift_pos X hX hBV).1
  let A : ℝ := q + (X.ν (Iio (0 : ℝ))).toReal
  let G : ℝ → ℝ := fun z => ∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν
  let F : ℝ → ℝ := fun t => ∫ z in (0 : ℝ)..t, W z
  let H : ℝ → ℝ := fun t => ∫ z in (0 : ℝ)..t, G z
  have hintW : IntervalIntegrable W volume (0 : ℝ) x :=
    scaleFunction_intervalIntegrable_nonnegative X q W hW 0 x (le_refl 0) (le_of_lt hx)
  have hcW : ContinuousAt W x :=
    scaleFunction_continuousAt_away_zero X q W hW x (ne_of_gt hx)
  have hmW : StronglyMeasurableAtFilter W (nhds x) volume :=
    (chat04_scaleFunction_measurable_of_punctured_continuity X q W hW).aestronglyMeasurable.stronglyMeasurableAtFilter
  have hF : HasDerivAt F (W x) x :=
    integral_hasDerivAt_right hintW hmW hcW
  have hGclosed : ContinuousOn G (Ici (0 : ℝ)) :=
    bv_finite_activity_scale_jump_convolution_continuous_nonnegative
      X hX q hq W hW hBV hFinite
  have hGint : IntervalIntegrable G volume (0 : ℝ) x := by
    apply ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hx)
    exact hGclosed.mono (by
      intro z hz
      exact (mem_Icc.mp hz).1)
  have hGpos : ContinuousOn G (Ioi (0 : ℝ)) :=
    bv_finite_activity_scale_jump_convolution_continuous_positive
      X hX q hq W hW hBV hFinite
  have hcG : ContinuousAt G x :=
    hGpos.continuousAt (isOpen_Ioi.mem_nhds hx)
  have hmG : StronglyMeasurableAtFilter G (nhds x) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun z hz => hGpos.continuousAt (isOpen_Ioi.mem_nhds hz)) x hx
  have hH : HasDerivAt H (G x) x :=
    integral_hasDerivAt_right hGint hmG hcG
  have hR : HasDerivAt (fun t => 1 + A * F t - H t)
      (A * W x - G x) x :=
    ((hF.const_mul A).const_add 1).sub hH
  have heq : (fun t => X.drift * W t) =ᶠ[nhds x]
      (fun t => 1 + A * F t - H t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
    simpa [A, F, G, H] using
      (bv_finite_activity_scale_volterra_integral_identity X hX q hq W hW
        hBV hFinite t ht)
  have hL : HasDerivAt (fun t => X.drift * W t) (A * W x - G x) x :=
    hR.congr_of_eventuallyEq heq
  have hscaled := hL.const_mul (X.drift)⁻¹
  have hfun : (fun t => X.drift⁻¹ * (X.drift * W t)) = W := by
    funext t
    simp [← mul_assoc, hd]
  rw [hfun] at hscaled
  rw [hscaled.deriv]
  simp [A, G, ← mul_assoc, hd]
