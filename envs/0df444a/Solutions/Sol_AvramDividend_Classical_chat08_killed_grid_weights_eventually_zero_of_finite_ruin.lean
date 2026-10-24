-- Prove2me | solution 1 for AvramDividend.Classical.chat08_killed_grid_weights_eventually_zero_of_finite_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:20:29.981157+00:00
-- url     : https://prove2.me/submissions/985adaaa-a8b6-47ba-9958-519c227f480e

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_stopped_record_grid_no_late_hit_of_finite_ruin
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! Finite reflected ruin makes the killed stopped first-record payment sequence eventually zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (ω : Ω)
    (a b h q : ℝ) (hh : 0 < h) (τ : ℝ≥0)
    (hτ : barrierRuinTime X a ω = (τ : ℝ≥0∞)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (if twoSidedExitUpTime X (b + (n : ℝ) * h) ω <
          barrierRuinTime X a ω then
         ENNReal.ofReal (h * Real.exp
           (-(q * (twoSidedExitUpTime X (b + (n : ℝ) * h) ω).toReal)))
       else 0) = 0 := by
  obtain ⟨N, hN⟩ := stopped_record_grid_no_late_hit_of_finite_ruin
    X ω a b h hh τ hτ
  refine ⟨N, ?_⟩
  intro n hn
  have hstop : ¬ twoSidedExitUpTime X (b + (n : ℝ) * h) ω <
      barrierRuinTime X a ω := by
    change ¬ (⨅ (r : ℝ≥0)
      (_ : b + (n : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) <
      barrierRuinTime X a ω
    exact hN n hn
  simp only [if_neg hstop]
