-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_scale_jump_primitive_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:23:14.378286+00:00
-- url     : https://prove2.me/submissions/aee6c458-02c9-48d8-af65-19139d79ab3f

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_continuous_nonnegative
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_continuous_positive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set intervalIntegral
open scoped NNReal ENNReal

/-- Integrating the continuous finite-jump convolution gives an antiderivative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ x : ℝ, 0 < x →
      deriv (fun t : ℝ =>
        ∫ z in (0 : ℝ)..t,
          (∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν)) x =
        ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν := by
  intro x hx
  let G : ℝ → ℝ := fun z => ∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν
  have hclosed : ContinuousOn G (Ici (0 : ℝ)) :=
    bv_finite_activity_scale_jump_convolution_continuous_nonnegative
      X hX q hq W hW hBV hFinite
  have hinterval : ContinuousOn G (Icc (0 : ℝ) x) := by
    apply hclosed.mono
    intro z hz
    exact (mem_Icc.mp hz).1
  have hint : IntervalIntegrable G volume (0 : ℝ) x :=
    ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hx) hinterval
  have hpositive : ContinuousOn G (Ioi (0 : ℝ)) :=
    bv_finite_activity_scale_jump_convolution_continuous_positive
      X hX q hq W hW hBV hFinite
  have hnhds : Ioi (0 : ℝ) ∈ nhds x := isOpen_Ioi.mem_nhds hx
  have hcont : ContinuousAt G x := hpositive.continuousAt hnhds
  have hmeas : StronglyMeasurableAtFilter G (nhds x) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun z hz => hpositive.continuousAt (isOpen_Ioi.mem_nhds hz)) x hx
  exact (integral_hasDerivAt_right hint hmeas hcont).deriv
