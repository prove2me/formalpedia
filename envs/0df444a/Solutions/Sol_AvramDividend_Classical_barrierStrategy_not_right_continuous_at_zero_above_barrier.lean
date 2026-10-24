-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_not_right_continuous_at_zero_above_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:30:20.934337+00:00
-- url     : https://prove2.me/submissions/70e3e477-3b43-486b-82b1-4b332fa217c2

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_rightLimit_eq_of_monotone_right_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_right_jump_positive
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Above the barrier, the initial excess payment prevents right continuity at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ha : 0 ≤ a) (hax : a < x) (ω : Ω) :
    ¬ ContinuousWithinAt
      (fun s => barrierStrategy X x a s ω) (Ici (0 : ℝ≥0)) 0 := by
  intro hcontinuous
  have hx : 0 ≤ x := le_trans ha (le_of_lt hax)
  have hstrategy : IsDividendStrategy 𝓕 (barrierStrategy X x a) :=
    barrierStrategy_isDividendStrategy_nonnegative_barrier X x a hx ha
  have hmono : Monotone (fun s : ℝ≥0 => barrierStrategy X x a s ω) :=
    hstrategy.2.1 ω
  have heq :=
    rightLimit_eq_of_monotone_right_continuous
      (barrierStrategy X x a) ω 0 hmono hcontinuous
  have hpos := barrierStrategy_initial_right_jump_positive X x a hax ω
  rw [heq, sub_self] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos
