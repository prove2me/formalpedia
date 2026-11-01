-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_verification_w_measurable_of_nonnegative_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:30:49.624701+00:00
-- url     : https://prove2.me/submissions/334c1d14-b266-4404-b3a5-bb68c6393480

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Nonnegative continuity and the killed negative branch make a BV
    verification test measurable on all real reserves. -/
theorem solution
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_neg : ∀ y < 0, w y = 0) : Measurable w := by
  classical
  have hpiece :
      Measurable ((Ici (0 : ℝ)).piecewise w (fun _ => (0 : ℝ))) :=
    ContinuousOn.measurable_piecewise
      hw_cont continuous_const.continuousOn measurableSet_Ici
  have heq :
      (Ici (0 : ℝ)).piecewise w (fun _ => (0 : ℝ)) = w := by
    funext y
    by_cases hy : 0 ≤ y
    · simp [Set.piecewise, hy]
    · have hyneg : y < 0 := lt_of_not_ge hy
      simp [Set.piecewise, hy, hw_neg y hyneg]
  simpa only [heq] using hpiece
