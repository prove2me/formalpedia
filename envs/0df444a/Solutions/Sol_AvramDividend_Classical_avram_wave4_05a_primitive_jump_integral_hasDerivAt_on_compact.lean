-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05a_primitive_jump_integral_hasDerivAt_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:36:06.822108+00:00
-- url     : https://prove2.me/submissions/ecb67c86-11b4-4a76-b87e-966696b41170

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_source_scale_primitive_global_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_contDiffOn_two_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_monotone_C2_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_primitive_kernel_hasDerivAt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

set_option maxHeartbeats 1000000

/-- Differentiation of the actual original Levy jump generator of the q-scale
primitive on a compact strictly-positive reserve interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (x : ℝ) (hx : x ∈ Ioo l u) :
    HasDerivAt
      (fun z : ℝ => ∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun v : ℝ => ∫ t in (0 : ℝ)..v, W t) z y ∂X.ν)
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) x := by
  let U : ℝ → ℝ := fun v => ∫ t in (0 : ℝ)..v, W t
  let μ : Measure ℝ := X.ν.restrict (Iio 0)
  let F : ℝ → ℝ → ℝ := fun z y =>
    SpectrallyNegativeLevy.generatorIntegrand U z y
  let G : ℝ → ℝ → ℝ := fun z y =>
    SpectrallyNegativeLevy.generatorIntegrand W z y
  have hWmono : Monotone W := scaleFunction_monotone X q W hW
  have hUmono : Monotone U :=
    avram_wave4_p2_source_scale_primitive_global_monotone X q W hW
  have hWnonneg : ∀ z : ℝ, 0 ≤ W z := by
    intro z
    by_cases hz : z < 0
    · rw [hW.1 z hz]
    · exact hW.2.1 z (le_of_not_gt hz)
  have hUnonneg : ∀ z : ℝ, 0 ≤ U z := by
    intro z
    by_cases hz : z ≤ 0
    · have heq : U z = 0 :=
        avram_wave4_p2_scale_primitive_zero_nonpositive X q W hW z hz
      rw [heq]
    · have h0z : 0 ≤ z := le_of_lt (lt_of_not_ge hz)
      have hmono := hUmono h0z
      simpa [U] using hmono
  have hUC2 : ContDiffOn ℝ 2 U (Ioo 0 a) := by
    apply (avram_wave4_p2_scale_primitive_contDiffOn_two_of_standing
      X hX q hq W hW).mono
    intro z hz
    exact hz.1
  obtain ⟨CW, hCWnonneg, hWbound⟩ :=
    avram_wave4_p3_generator_integrand_uniform_monotone_C2_quadratic_bound
      X W hWnonneg hWmono a l u hl hlu hu hC2
  obtain ⟨CU, hCUnonneg, hUbound⟩ :=
    avram_wave4_p3_generator_integrand_uniform_monotone_C2_quadratic_bound
      X U hUnonneg hUmono a l u hl hlu hu hUC2
  have hmin_meas :
      AEStronglyMeasurable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by
    fun_prop
  have hmin_nonneg :
      0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) := by
    filter_upwards with y
    positivity
  have hmin_full :
      Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hmin_meas hmin_nonneg).mp (ne_of_lt X.ν_integrable)
  have hmin : Integrable (fun y : ℝ => min 1 (y ^ 2)) μ :=
    hmin_full.mono_measure Measure.restrict_le_self
  have hBoundW : Integrable (fun y : ℝ => CW * min 1 (y ^ 2)) μ :=
    hmin.const_mul CW
  have hBoundU : Integrable (fun y : ℝ => CU * min 1 (y ^ 2)) μ :=
    hmin.const_mul CU
  have hind :
      Measurable
        (fun y : ℝ =>
          (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) :=
    measurable_const.indicator measurableSet_Ioo
  have hFmeas : ∀ z : ℝ, AEStronglyMeasurable (F z) μ := by
    intro z
    have hshift : Measurable (fun y : ℝ => U (z + y)) :=
      hUmono.measurable.comp (measurable_const.add measurable_id)
    have hmeas : Measurable (F z) := by
      unfold F SpectrallyNegativeLevy.generatorIntegrand
      exact (hshift.sub measurable_const).sub
        ((measurable_const.mul measurable_id).mul hind)
    exact hmeas.aestronglyMeasurable
  have hGmeas : AEStronglyMeasurable (G x) μ := by
    have hshift : Measurable (fun y : ℝ => W (x + y)) :=
      hWmono.measurable.comp (measurable_const.add measurable_id)
    have hmeas : Measurable (G x) := by
      unfold G SpectrallyNegativeLevy.generatorIntegrand
      exact (hshift.sub measurable_const).sub
        ((measurable_const.mul measurable_id).mul hind)
    exact hmeas.aestronglyMeasurable
  have hxIcc : x ∈ Icc l u := ⟨hx.1.le, hx.2.le⟩
  have hFbound : ∀ᵐ y ∂μ, ‖F x y‖ ≤ CU * min 1 (y ^ 2) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := X.ν) measurableSet_Iio] with y hy
    exact hUbound x hxIcc y hy
  have hFint : Integrable (F x) μ :=
    hBoundU.mono' (hFmeas x) hFbound
  have hGbound : ∀ᵐ y ∂μ, ∀ z ∈ Ioo l u,
      ‖G z y‖ ≤ CW * min 1 (y ^ 2) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := X.ν) measurableSet_Iio] with y hy z hz
    exact hWbound z ⟨hz.1.le, hz.2.le⟩ y hy
  have hDerivative : ∀ᵐ y ∂μ, ∀ z ∈ Ioo l u,
      HasDerivAt (fun v : ℝ => F v y) (G z y) z := by
    filter_upwards with y z hz
    exact avram_wave4_05a_primitive_kernel_hasDerivAt
      X hX hnbv q hq W hW z y (hl.trans hz.1)
  have hFmeas_ev : ∀ᶠ z : ℝ in nhds x,
      AEStronglyMeasurable (F z) μ :=
    Filter.Eventually.of_forall hFmeas
  have hRes :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (s := Ioo l u)
      (bound := fun y : ℝ => CW * min 1 (y ^ 2))
      (F := F) (F' := G) (x₀ := x)
      (isOpen_Ioo.mem_nhds hx)
      hFmeas_ev hFint hGmeas hGbound hBoundW hDerivative
  simpa only [F, G, U, μ, MeasureTheory.integral] using hRes.2
