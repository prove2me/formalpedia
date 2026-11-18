-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_source_original_negative_Borel_count_HasLaw_of_true_count_20261118
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:31:17.81502+00:00
-- url     : https://prove2.me/submissions/7025a940-6923-4818-a415-8252a92218e8

import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a114_original_negative_Borel_count_exact_poisson_singleton_probabilities_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal)
    (r : ℝ≥0)
    (hr : (r : ℝ) = ((T : ℝ≥0∞) * X.ν B).toReal) :
    HasLaw K (poissonMeasure r) P := by
  have hMass :=
    avram_a114_original_negative_Borel_count_exact_poisson_singleton_probabilities_20261114
      X hFinite T B hB hNeg K hK hCount r hr
  refine ⟨hK.aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply hK (measurableSet_singleton k)]
  exact hMass k
