-- Prove2me | solution 1 for AvramDividend.Classical.canonical_drifted_brownian_natural_adapted
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:45:17.427976+00:00
-- url     : https://prove2.me/submissions/3cc56ee1-5b47-4008-a2fe-4bdcdceb0638

import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_measurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Tactic

open ProbabilityTheory MeasureTheory
open scoped NNReal

theorem solution :
    let X : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun t ω =>
      ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω - (t : ℝ)
    ∃ hmeas : ∀ t : ℝ≥0, StronglyMeasurable (X t),
      Adapted (Filtration.natural X hmeas) X := by
  intro X
  have hmeas : ∀ t : ℝ≥0, StronglyMeasurable (X t) := fun t =>
    (AvramDividend.Classical.canonical_drifted_brownian_measurable t).stronglyMeasurable
  exact ⟨hmeas, fun t => (Filtration.stronglyAdapted_natural hmeas t).measurable⟩
