-- Prove2me | solution 1 for AvramDividend.Classical.stopped_record_grid_no_late_hit_of_finite_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:02:06.816845+00:00
-- url     : https://prove2.me/submissions/1a81c4cd-a7a2-4c80-8f90-6ecd3179cc71

import Mathlib.Data.Real.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_record_grid_clocks_eventually_ge_horizon
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-! On every path with finite reflected ruin time, only finitely many record levels can be attained strictly before ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (ω : Ω)
    (a b h : ℝ) (hh : 0 < h) (τ : ℝ≥0)
    (hτ : barrierRuinTime X a ω = (τ : ℝ≥0∞)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ¬ (⨅ (r : ℝ≥0) (_ : b + (n : ℝ) * h < X.X r ω), (r : ℝ≥0∞))
        < barrierRuinTime X a ω := by
  obtain ⟨N, hN⟩ :=
    firstUpcrossing_record_grid_clocks_eventually_ge_horizon X ω τ b h hh
  refine ⟨N, ?_⟩
  intro n hn
  rw [hτ]
  exact not_lt_of_ge (hN n hn)
