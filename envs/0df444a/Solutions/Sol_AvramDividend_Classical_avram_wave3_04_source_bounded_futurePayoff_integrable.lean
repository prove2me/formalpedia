-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_source_bounded_futurePayoff_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:31:04.121346+00:00
-- url     : https://prove2.me/submissions/f254c0e8-9d24-4ada-bbe6-fcb86e1e84c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every bounded Borel payoff of an original Lévy increment has a
finite first absolute moment, regardless of Lévy first-moment existence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (K : ℝ) (hBound : ∀ y, ‖φ y‖ ≤ K) :
    Integrable (fun ω => φ (X.X t ω)) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  exact Integrable.of_bound (hφ.comp hXt).aestronglyMeasurable K
    (Filter.Eventually.of_forall (fun ω => hBound (X.X t ω)))
