-- Prove2me | solution 1 for AvramDividend.Classical.levy_measurableSet_early_negative_before_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:31:06.445276+00:00
-- url     : https://prove2.me/submissions/01c1329f-2378-42f2-9ea9-1a26bf1c8344

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_negative_before_horizon_iff_dense_grid
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.MeasurableSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (times : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (ε : ℝ≥0) :
    MeasurableSet[𝓕 ε]
      {ω : Ω | ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0} := by
  have hEq :
      {ω : Ω | ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0} =
      (⋃ m : ℕ,
        {ω : Ω | times m < ε ∧ X.X (times m) ω < 0}) := by
    ext ω
    simpa only [Set.mem_setOf_eq, Set.mem_iUnion] using
      (levy_negative_before_horizon_iff_dense_grid
        X times hdense ω ε)
  rw [hEq]
  refine MeasurableSet.iUnion fun m => ?_
  by_cases h : times m < ε
  · have hm : MeasurableSet[𝓕 ε]
        {ω : Ω | X.X (times m) ω < 0} :=
      isOpen_Iio.measurableSet.preimage
        (X.adapted.measurable_le (le_of_lt h))
    simpa only [h, true_and] using hm
  · simp [h]
