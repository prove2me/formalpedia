-- Prove2me | solution 1 for AvramDividend.Classical.chat03_nonnegative_truncated_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:00:12.017551+00:00
-- url     : https://prove2.me/submissions/ec3f5334-03d1-46c7-b3b8-edad6ed6c481

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-!
Every nonnegative random variable truncated at a finite nonnegative
threshold is integrable on a probability space.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hYm : AEStronglyMeasurable Y P)
    (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω) :
    Integrable (fun ω => min (Y ω) R) P := by
  have hc : Continuous (fun y : ℝ => min y R) :=
    continuous_id.min continuous_const
  have hmeas : AEStronglyMeasurable (fun ω => min (Y ω) R) P :=
    hc.comp_aestronglyMeasurable hYm
  apply Integrable.of_bound hmeas R
  filter_upwards [hY0] with ω hy
  have hmin0 : 0 ≤ min (Y ω) R := le_min hy hR
  simpa [Real.norm_eq_abs, abs_of_nonneg hmin0] using
    (min_le_right (Y ω) R)
