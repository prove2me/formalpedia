-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_scale_derivative_jump_convolution_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:27:18.575777+00:00
-- url     : https://prove2.me/submissions/2f239571-ff45-4f96-833f-f48975b7778c

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
  let A : ℝ := q + (X.ν (Iio (0 : ℝ))).toReal
  let F : ℝ → ℝ := fun t => ∫ z in (0 : ℝ)..t, W z
  let G : ℝ → ℝ := fun z => ∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν
  let H : ℝ → ℝ := fun t => ∫ z in (0 : ℝ)..t, G z
  have hDne : X.drift ≠ 0 := ne_of_gt (bv_standing_drift_pos X hX hBV).1
  intro x hx
  have hFI : IntervalIntegrable W volume (0 : ℝ) x :=
    scaleFunction_intervalIntegrable_nonnegative X q W hW 0 x (le_refl _) (le_of_lt hx)
  have hFc : ContinuousAt W x :=
    scaleFunction_continuousAt_away_zero X q W hW x (ne_of_gt hx)
  have hFm : StronglyMeasurableAtFilter W (nhds x) volume :=
    (chat04_scaleFunction_measurable_of_punctured_continuity X q W hW).aestronglyMeasurable.stronglyMeasurableAtFilter
  have hFd : HasDerivAt F (W x) x :=
    integral_hasDerivAt_right hFI hFm hFc
  have hGclosed : ContinuousOn G (Ici (0 : ℝ)) :=
    bv_finite_activity_scale_jump_convolution_continuous_nonnegative
      X hX q hq W hW hBV hFinite
  have hGcompact : ContinuousOn G (Icc (0 : ℝ) x) := by
    apply hGclosed.mono
    intro z hz
    exact hz.1
  have hGI : IntervalIntegrable G volume (0 : ℝ) x :=
    ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hx) hGcompact
  have hGpositive : ContinuousOn G (Ioi (0 : ℝ)) :=
    bv_finite_activity_scale_jump_convolution_continuous_positive
      X hX q hq W hW hBV hFinite
  have hGc : ContinuousAt G x :=
    hGpositive.continuousAt (isOpen_Ioi.mem_nhds (mem_Ioi.mpr hx))
  have hGm : StronglyMeasurableAtFilter G (nhds x) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hGpositive x (mem_Ioi.mpr hx)
  have hHd : HasDerivAt H (G x) x :=
    integral_hasDerivAt_right hGI hGm hGc
  have hRight : HasDerivAt (fun t => 1 + A * F t - H t)
      (A * W x - G x) x := ((hFd.const_mul A).const_add 1).sub hHd
  have hDiv : HasDerivAt (fun t => (1 + A * F t - H t) / X.drift)
      ((A * W x - G x) / X.drift) x :=
    hRight.div_const X.drift
  have hEq : W =ᶠ[nhds x] (fun t => (1 + A * F t - H t) / X.drift) := by
    filter_upwards [isOpen_Ioi.mem_nhds (mem_Ioi.mpr hx)] with t ht
    have hVol :=
      bv_finite_activity_scale_volterra_integral_identity
        X hX q hq W hW hBV hFinite t (mem_Ioi.mp ht)
    change X.drift * W t = 1 + A * F t - H t at hVol
    apply (eq_div_iff hDne).2
    nlinarith
  have hWd : HasDerivAt W ((A * W x - G x) / X.drift) x :=
    hDiv.congr_of_eventuallyEq hEq
  change X.drift * deriv W x = A * W x - G x
  rw [hWd.deriv]
  field_simp [hDne]
