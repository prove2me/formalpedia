-- Prove2me | solution 1 for AvramDividend.Classical.chat04_countable_future_path_barrier_survival_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:23:44.744359+00:00
-- url     : https://prove2.me/submissions/39505276-5680-4258-be4a-60a5fc182303

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-!
Measurable future-path two-barrier survival on an arbitrary countable
schedule up to T, as a subset of the FULL function space (R≥0→R).
This avoids treating an uncountable intersection as automatically Borel.
-/
theorem solution
    (τ : ℕ → ℝ≥0) (T : ℝ≥0)
    (lower upper : ℝ) :
    MeasurableSet
      {y : ℝ≥0 → ℝ | ∀ j : ℕ, τ j ≤ T →
        ¬ (y (τ j) < lower ∨ upper < y (τ j))} := by
  have hOne : ∀ j : ℕ, MeasurableSet
      {y : ℝ≥0 → ℝ | τ j ≤ T →
        ¬ (y (τ j) < lower ∨ upper < y (τ j))} := by
    intro j
    have heval : Measurable (fun y : ℝ≥0 → ℝ => y (τ j)) :=
      measurable_pi_apply (τ j)
    have hl : MeasurableSet {y : ℝ≥0 → ℝ | y (τ j) < lower} := by
      change MeasurableSet
        ((fun y : ℝ≥0 → ℝ => y (τ j)) ⁻¹' Set.Iio lower)
      exact isOpen_Iio.measurableSet.preimage heval
    have hu : MeasurableSet {y : ℝ≥0 → ℝ | upper < y (τ j)} := by
      change MeasurableSet
        ((fun y : ℝ≥0 → ℝ => y (τ j)) ⁻¹' Set.Ioi upper)
      exact isOpen_Ioi.measurableSet.preimage heval
    have hClosed : MeasurableSet
        {y : ℝ≥0 → ℝ | ¬ (y (τ j) < lower ∨ upper < y (τ j))} := by
      have heq :
          {y : ℝ≥0 → ℝ |
            ¬ (y (τ j) < lower ∨ upper < y (τ j))} =
          ({y : ℝ≥0 → ℝ | y (τ j) < lower} ∪
            {y : ℝ≥0 → ℝ | upper < y (τ j)})ᶜ := by
        ext y
        simp
      rw [heq]
      exact (hl.union hu).compl
    by_cases hj : τ j ≤ T
    · simpa only [hj, true_implies] using hClosed
    · simp [hj]
  have hEq :
      {y : ℝ≥0 → ℝ | ∀ j : ℕ, τ j ≤ T →
        ¬ (y (τ j) < lower ∨ upper < y (τ j))} =
      ⋂ j : ℕ, {y : ℝ≥0 → ℝ | τ j ≤ T →
        ¬ (y (τ j) < lower ∨ upper < y (τ j))} := by
    ext y
    simp
  rw [hEq]
  exact MeasurableSet.iInter hOne
