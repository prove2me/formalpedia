-- Prove2me | solution 1 for AvramDividend.Classical.chat04_countable_shifted_future_reserve_survival_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:26:57.272143+00:00
-- url     : https://prove2.me/submissions/eda13e41-d1cb-4f99-be3a-5b56612ac09b

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Countably monitored survival is Borel for a variable reserve and future path. -/
theorem solution
    (τ : ℕ → ℝ≥0) (T : ℝ≥0) :
    MeasurableSet
      {z : ℝ × (ℝ≥0 → ℝ) |
        ∀ j : ℕ, τ j ≤ T → 0 ≤ z.1 + z.2 (τ j)} := by
  have hOne : ∀ j : ℕ, MeasurableSet
      {z : ℝ × (ℝ≥0 → ℝ) |
        τ j ≤ T → 0 ≤ z.1 + z.2 (τ j)} := by
    intro j
    have heval : Measurable
        (fun z : ℝ × (ℝ≥0 → ℝ) => z.1 + z.2 (τ j)) :=
      measurable_fst.add ((measurable_pi_apply (τ j)).comp measurable_snd)
    have hClosed : MeasurableSet
        {z : ℝ × (ℝ≥0 → ℝ) | 0 ≤ z.1 + z.2 (τ j)} := by
      change MeasurableSet
        ((fun z : ℝ × (ℝ≥0 → ℝ) => z.1 + z.2 (τ j)) ⁻¹' Set.Ici 0)
      exact isClosed_Ici.measurableSet.preimage heval
    by_cases hj : τ j ≤ T
    · simpa only [hj, true_implies] using hClosed
    · simp [hj]
  have hEq :
      {z : ℝ × (ℝ≥0 → ℝ) |
        ∀ j : ℕ, τ j ≤ T → 0 ≤ z.1 + z.2 (τ j)} =
      ⋂ j : ℕ, {z : ℝ × (ℝ≥0 → ℝ) |
        τ j ≤ T → 0 ≤ z.1 + z.2 (τ j)} := by
    ext z
    simp
  rw [hEq]
  exact MeasurableSet.iInter hOne
