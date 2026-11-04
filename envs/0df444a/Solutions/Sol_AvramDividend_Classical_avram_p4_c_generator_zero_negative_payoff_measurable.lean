-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_zero_negative_payoff_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:13:31.709676+00:00
-- url     : https://prove2.me/submissions/cc047d26-3d4f-445b-a660-48e79068ae3e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical

theorem solution
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0) :
    Measurable w := by
  have hpiece : Measurable ((Ici (0 : ℝ)).piecewise w (fun _ : ℝ => (0 : ℝ))) :=
    hw_cont.measurable_piecewise continuousOn_const measurableSet_Ici
  have heq : (Ici (0 : ℝ)).piecewise w (fun _ : ℝ => (0 : ℝ)) = w := by
    funext y
    by_cases hy : 0 ≤ y
    · simp [Set.piecewise, hy]
    · have hyn : y < 0 := lt_of_not_ge hy
      simp [Set.piecewise, hy, hw_neg y hyn]
  simpa only [heq] using hpiece
