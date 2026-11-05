-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_zero_negative_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:29:56.970546+00:00
-- url     : https://prove2.me/submissions/4cd7eb6e-df1f-49d4-8890-e1fc59a7294e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (hneg : ∀ y : ℝ, y < 0 → w y = 0) : Measurable w := by
  classical
  have hconst : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Ici (0 : ℝ))ᶜ :=
    continuous_const.continuousOn
  have hpiece : Measurable ((Ici (0 : ℝ)).piecewise w (fun _ => (0 : ℝ))) :=
    ContinuousOn.measurable_piecewise hw hconst measurableSet_Ici
  have heq : (Ici (0 : ℝ)).piecewise w (fun _ => (0 : ℝ)) = w := by
    funext y
    by_cases hy : 0 ≤ y
    · simp [Set.piecewise, Set.mem_Ici, hy]
    · have hlt : y < 0 := lt_of_not_ge hy
      simp [Set.piecewise, Set.mem_Ici, hy, hneg y hlt]
  rw [heq] at hpiece
  exact hpiece
