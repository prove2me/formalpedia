-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_weighted_jump_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:46:51.869801+00:00
-- url     : https://prove2.me/submissions/be9b5526-7c60-4011-b301-bd106fa70d9d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_uniform_negative_jump_min_sq
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (V ρ : ℝ → ℝ) (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hVmono : Monotone V) (hVnonneg : ∀ t, 0 ≤ V t)
    (hV : ContDiffOn ℝ 2 V (Ioo 0 a))
    (hρ : Integrable ρ) (hρm : Measurable ρ)
    (hs : ∀ᵐ r ∂volume, ρ r ≠ 0 → a - r ∈ Icc l u) :
    Integrable (fun p : ℝ × ℝ => ρ p.1 *
      SpectrallyNegativeLevy.generatorIntegrand V (a - p.1) p.2)
      (volume.prod (X.ν.restrict (Iio 0))) := by 
  let ν := X.ν.restrict (Iio 0)
  letI : SFinite ν := levy_negative_jump_measure_sFinite X
  obtain ⟨K, hK, hb⟩ := avram_locmoll_uniform_negative_jump_min_sq
    X V a l u hl hlu hu hVmono hVnonneg hV
  have hm : Integrable (fun z : ℝ => min 1 (z ^ 2)) X.ν :=
    (lintegral_ofReal_ne_top_iff_integrable
      (by fun_prop : AEStronglyMeasurable (fun z : ℝ => min 1 (z ^ 2)) X.ν)
      (Filter.Eventually.of_forall (fun z => by positivity))).mp (ne_of_lt X.ν_integrable)
  have hdom := (hρ.norm.const_mul K).mul_prod (hm.mono_measure
    (Measure.restrict_le_self : ν ≤ X.ν))
  have hVmeas := hVmono.measurable
  have hdmeas := measurable_deriv V
  have htrunc : Measurable ((Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
    measurable_const.indicator measurableSet_Ioo
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 *
      SpectrallyNegativeLevy.generatorIntegrand V (a - p.1) p.2)
      (volume.prod ν) := by
    apply Measurable.aestronglyMeasurable
    unfold SpectrallyNegativeLevy.generatorIntegrand
    fun_prop
  refine hdom.mono hmeas ?_
  have hs' : ∀ᵐ p ∂volume.prod ν, ρ p.1 ≠ 0 → a - p.1 ∈ Icc l u :=
    (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := ν)).tendsto_ae.eventually hs
  have hz' : ∀ᵐ p : ℝ × ℝ ∂volume.prod ν, p.2 < 0 :=
    (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := ν)).tendsto_ae.eventually
      (ae_restrict_mem measurableSet_Iio)
  filter_upwards [hs', hz'] with p hp hz
  by_cases hzero : ρ p.1 = 0
  · simp [hzero]
  · have hh := hb (a - p.1) (hp hzero) p.2 hz
    rw [norm_mul, Real.norm_eq_abs (K * ‖ρ p.1‖ * min 1 (p.2 ^ 2)),
      abs_of_nonneg (by positivity)]
    calc
      _ ≤ ‖ρ p.1‖ * (K * min 1 (p.2 ^ 2)) :=
        mul_le_mul_of_nonneg_left hh (norm_nonneg _)
      _ = _ := by ring
