-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_predictable_negative_kernel_L1_from_min_mark_weight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:08:59.415994+00:00
-- url     : https://prove2.me/submissions/aa65fca7-7752-4203-885a-2bc0108e2f1b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_min_one_abs_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_predictable_mark_kernel_L1_from_physical_mark_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true BV small negative jump first moment yields global predictable marked L¹ under a uniform finite C¹-envelope weight. -/
theorem solution
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
  (hμ : μ Set.univ < ⊤)
  (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
  (hGm : Measurable[(@Prod.instMeasurableSpace _ _
    (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G)
  (L : ℝ)
  (hBound : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
    𝓕.rightCont.predictable;
    ∀ᵐ p ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))),
      ‖G p‖ ≤ ‖L * min 1 |p.2|‖)) :
  (letI : MeasurableSpace (ℝ≥0 × Ω) :=
    𝓕.rightCont.predictable;
    Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
  have hmin : Integrable (fun z : ℝ => min 1 |z|)
      (X.ν.restrict (Iio (0 : ℝ))) :=
    boundedVariation_min_one_abs_integrable X hBV
  have hg : Integrable (fun z : ℝ => L * min 1 |z|)
      (X.ν.restrict (Iio (0 : ℝ))) := hmin.const_mul L
  exact avram_wave7_02_original_predictable_mark_kernel_L1_from_physical_mark_envelope
    X μ hμ (fun z => L * min 1 |z|) hg G
    hGm.aestronglyMeasurable hBound
