-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_predictable_finite_band_bounded_kernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:01:41.641873+00:00
-- url     : https://prove2.me/submissions/2fe34559-e91e-4d24-8923-75e1d2330d27

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Bounded predictable kernels have finite energy against the original
    finite-band physical-time Levy compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμfinite : μ Set.univ < ∞)
    (hνfinite : X.ν (Iic (-(1 / ((n : ℝ) + 1)))) < ∞)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGmeas : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G)
    (C : ℝ) (hC : 0 ≤ C)
    (hGbounded : ∀ p, |G p| ≤ C) :
    Integrable G (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      μ.prod (X.ν.restrict (Iic (-(1 / ((n : ℝ) + 1)))))) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  haveI : IsFiniteMeasure μ := ⟨hμfinite⟩
  haveI : IsFiniteMeasure (X.ν.restrict B) := by
    constructor
    simpa [B] using hνfinite
  change Integrable G (μ.prod (X.ν.restrict B))
  haveI : IsFiniteMeasure (μ.prod (X.ν.restrict B)) := inferInstance
  apply Integrable.of_bound hGmeas.aestronglyMeasurable C
  filter_upwards [] with p
  rw [Real.norm_eq_abs]
  exact hGbounded p
