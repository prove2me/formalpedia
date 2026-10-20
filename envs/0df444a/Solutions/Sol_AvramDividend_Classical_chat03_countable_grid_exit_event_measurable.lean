-- Prove2me | solution 1 for AvramDividend.Classical.chat03_countable_grid_exit_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T23:05:32.894767+00:00
-- url     : https://prove2.me/submissions/7423aa4e-dae7-42c4-a7be-b46efc5b40eb

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_fixed_inverse_nat_grid_exit_measurable
import Mathlib.MeasureTheory.MeasurableSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
All inverse-natural grid crossings constitute a countable union of
measurable fixed-time events. This is independent of the pathwise
right-continuity equivalence with a continuous-time strict crossing.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) :
    MeasurableSet {ω : Ω | ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower ∨
      upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω} := by
  have hGrid : ∀ n : ℕ, MeasurableSet
      {ω : Ω | ∃ k : ℕ,
        X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower ∨
        upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω} := by
    intro n
    simpa only [Set.iUnion_setOf] using
      (MeasurableSet.iUnion (fun k : ℕ =>
        chat03_fixed_inverse_nat_grid_exit_measurable X lower upper n k))
  have hOuter : ∀ n : ℕ, MeasurableSet
      {ω : Ω | 0 < n ∧ ∃ k : ℕ,
        X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower ∨
        upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω} := by
    intro n
    by_cases hn : 0 < n
    · simpa only [hn, true_and] using hGrid n
    · simpa only [hn, false_and, setOf_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  simpa only [Set.iUnion_setOf] using (MeasurableSet.iUnion hOuter)

