-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrand_compact_prod_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:54:10.00899+00:00
-- url     : https://prove2.me/submissions/83c942f0-67c8-464b-8f80-c2a627f2a633

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_uniform_generatorIntegrand_bound_on_compact
import Theorems.Thm_AvramDividend_Classical_scaleFunction_compensated_increment_extension_measurable
import Theorems.Thm_AvramDividend_Classical_integrable_prod_of_uniform_min_sq_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable
      ((Icc l u ×ˢ Iio (0 : ℝ)).indicator
        (fun p : ℝ × ℝ =>
          SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2))
      (μ.prod (X.ν.restrict (Iio 0))) := by
  let s : Set (ℝ × ℝ) := Icc l u ×ˢ Iio (0 : ℝ)
  let f : ℝ × ℝ → ℝ := fun p =>
    SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2
  let e : ℝ × ℝ → ℝ := fun p =>
    W (p.1 + p.2) - W p.1 -
    ((Ioo 0 a).indicator (deriv W) p.1) * p.2 *
      ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) p.2)
  have he : Measurable e :=
    scaleFunction_compensated_increment_extension_measurable X q W hW a hC2
  have hs : MeasurableSet s :=
    measurableSet_Icc.prod measurableSet_Iio
  have heq : s.indicator f = s.indicator e := by
    funext p
    by_cases hp : p ∈ s
    · have hx : p.1 ∈ Icc l u := hp.1
      have hxa : p.1 ∈ Ioo 0 a :=
        ⟨lt_of_lt_of_le hl hx.1, lt_of_le_of_lt hx.2 hu⟩
      simp only [Set.indicator_of_mem hp]
      dsimp [f, e]
      unfold SpectrallyNegativeLevy.generatorIntegrand
      rw [Set.indicator_of_mem hxa]
      simp only [Pi.one_def]
    · simp [Set.indicator, hp]
  have hmeas : AEStronglyMeasurable (s.indicator f)
      (μ.prod (X.ν.restrict (Iio 0))) := by
    rw [heq]
    exact (he.indicator hs).aestronglyMeasurable
  obtain ⟨C, hC, hbound⟩ :=
    scaleFunction_uniform_generatorIntegrand_bound_on_compact
      X q W hW a l u hl hlu hu hC2
  have hmin_meas :
      AEStronglyMeasurable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by
    fun_prop
  have hmin_nonneg :
      0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) := by
    filter_upwards with y
    positivity
  have hminfull :
      Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hmin_meas hmin_nonneg).mp (ne_of_lt X.ν_integrable)
  have hmin :
      Integrable (fun y : ℝ => min 1 (y ^ 2))
        (X.ν.restrict (Iio 0)) :=
    hminfull.mono_measure Measure.restrict_le_self
  have hglobal : ∀ p : ℝ × ℝ,
      ‖s.indicator f p‖ ≤ C * min 1 (p.2 ^ 2) := by
    intro p
    by_cases hp : p ∈ s
    · simp only [Set.indicator_of_mem hp]
      exact hbound p.1 hp.1 p.2 hp.2
    · have hm : 0 ≤ min (1 : ℝ) (p.2 ^ 2) := by positivity
      have hpos : 0 ≤ C * min 1 (p.2 ^ 2) :=
        mul_nonneg hC hm
      simpa [Set.indicator, hp] using hpos
  exact integrable_prod_of_uniform_min_sq_bound
    μ (X.ν.restrict (Iio 0)) hmin (s.indicator f) hmeas C hC hglobal
