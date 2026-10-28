-- Prove2me | solution 2 for AvramDividend.Classical.bv_finite_activity_scale_jump_primitive_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:23:52.83498+00:00
-- url     : https://prove2.me/submissions/72be6901-fac3-4afd-a7ae-96cd618e9037

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_continuous_positive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Order.LeftRight

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
      deriv (fun t : ℝ =>
        ∫ z in (0 : ℝ)..t,
          (∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν)) x =
        ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν := by
  let G : ℝ → ℝ :=
    fun z => ∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν
  have hGzero : G 0 = 0 := by
    have hneg : ∀ᵐ y : ℝ ∂X.ν.restrict (Iio (0 : ℝ)), y < 0 := by
      simpa only [mem_Iio] using
        (ae_restrict_mem (μ := X.ν) measurableSet_Iio)
    have hzero :
        (fun y : ℝ => W (0 + y)) =ᵐ[X.ν.restrict (Iio (0 : ℝ))]
          (fun _ => (0 : ℝ)) := by
      filter_upwards [hneg] with y hy
      simpa only [zero_add] using hW.1 y hy
    change (∫ y in Iio (0 : ℝ), W (0 + y) ∂X.ν) = 0
    rw [integral_congr_ae hzero]
    simp
  have hGright : ContinuousWithinAt G (Ioi (0 : ℝ)) 0 := by
    rw [ContinuousWithinAt]
    rw [hGzero]
    exact bv_finite_activity_scale_jump_convolution_tendsto_zero
      X hX q hq W hW hBV hFinite
  have hGpos : ContinuousOn G (Ioi (0 : ℝ)) :=
    bv_finite_activity_scale_jump_convolution_continuous_positive
      X hX q hq W hW hBV hFinite
  have hGnonneg : ContinuousOn G (Ici (0 : ℝ)) := by
    intro z hz
    rcases eq_or_lt_of_le (mem_Ici.mp hz) with hzero | hpos
    · subst z
      exact (continuousWithinAt_Ioi_iff_Ici).mp hGright
    · have hzmem : z ∈ Ioi (0 : ℝ) := mem_Ioi.mpr hpos
      have hc : ContinuousAt G z :=
        hGpos.continuousAt (isOpen_Ioi.mem_nhds hzmem)
      exact hc.continuousWithinAt
  intro x hx
  have hGu : ContinuousOn G (uIcc (0 : ℝ) x) := by
    apply hGnonneg.mono
    intro z hz
    rw [uIcc_of_le (le_of_lt hx)] at hz
    exact hz.1
  have hGI : IntervalIntegrable G volume (0 : ℝ) x :=
    hGu.intervalIntegrable
  have hGat : ContinuousAt G x :=
    hGpos.continuousAt (isOpen_Ioi.mem_nhds (mem_Ioi.mpr hx))
  have hSM : StronglyMeasurableAtFilter G (nhds x) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hGpos x (mem_Ioi.mpr hx)
  change deriv (fun t : ℝ => ∫ z in (0 : ℝ)..t, G z) x = G x
  exact (intervalIntegral.integral_hasDerivAt_right hGI hSM hGat).deriv
