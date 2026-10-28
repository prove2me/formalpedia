-- Prove2me | solution 1 for AvramDividend.Classical.extendedStopping_truncate_finite_leEvents
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:45:50.855562+00:00
-- url     : https://prove2.me/submissions/521a312d-59e5-4e03-bdb7-b459540a384b

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Truncating a possibly infinite stopping clock yields a finite
    nonnegative stopping clock with observable lower-level events. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (n : ℝ≥0) :
    ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s]
        {ω : Ω | (min (τ ω) (n : ℝ≥0∞)).toNNReal ≤ s} := by
  intro s
  have hmin : IsStoppingTime 𝓕
      (fun ω : Ω => min (τ ω) (n : ℝ≥0∞)) :=
    hτ.min_const n
  have hcast (ω : Ω) :
      ((min (τ ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0∞) =
        min (τ ω) (n : ℝ≥0∞) := by
    apply ENNReal.coe_toNNReal
    have hlt : min (τ ω) (n : ℝ≥0∞) < (⊤ : ℝ≥0∞) :=
      lt_of_le_of_lt (min_le_right _ _) (by simp)
    exact ne_of_lt hlt
  have hset :
      {ω : Ω | (min (τ ω) (n : ℝ≥0∞)).toNNReal ≤ s} =
        {ω : Ω | min (τ ω) (n : ℝ≥0∞) ≤ (s : ℝ≥0∞)} := by
    ext ω
    constructor
    · intro hw
      have hh :
          ((min (τ ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0∞) ≤
            (s : ℝ≥0∞) :=
        (ENNReal.coe_le_coe).2 hw
      simpa only [Set.mem_setOf_eq, hcast ω] using hh
    · intro hw
      apply (ENNReal.coe_le_coe).1
      simpa only [Set.mem_setOf_eq, hcast ω] using hw
  rw [hset]
  exact hmin s