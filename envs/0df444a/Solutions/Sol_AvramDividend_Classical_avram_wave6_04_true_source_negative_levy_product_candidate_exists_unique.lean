-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_true_source_negative_levy_product_candidate_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:54:36.64091+00:00
-- url     : https://prove2.me/submissions/f53e9c3b-5c7f-4eb2-bcf5-8d6164ee6d8c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_clock_trim_to_predictable_exists_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_predictable_clock_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The uniquely determined finite-horizon negative-source Lévy
product measure is a candidate compensator. The source jump-intensity
identity remains the separate Chat 01 obligation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    ∃! N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)),
      ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
        μ Set.univ < ⊤ ∧
        (∀ A : Set (ℝ≥0 × Ω),
          MeasurableSet[𝓕.rightCont.predictable] A →
          μ A =
            ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
              Real.toNNReal).prod P) A) ∧
        N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
                  𝓕.rightCont.predictable
             μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := by
  obtain ⟨μ, hfinite, hclock⟩ :=
    avram_wave6_04_true_source_physical_clock_trim_to_predictable_exists_finite
      (P := P) 𝓕 T
  refine ⟨(letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable
    μ.prod (X.ν.restrict (Iio (0 : ℝ)))), ⟨μ, hfinite, hclock, rfl⟩, ?_⟩
  rintro N' ⟨μ', hfinite', hclock', hN'⟩
  have hμ : μ' = μ :=
    avram_wave6_04_true_source_physical_predictable_clock_unique
      𝓕 T μ' μ hclock' hclock
  subst μ'
  exact hN'
