-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a533_one_sided_three_source_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:20:06.942912+00:00
-- url     : https://prove2.me/submissions/9f3e4f85-dea9-4780-a7b9-f5bbbf351797

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (A B C : Ω → ℝ)
    (hA : Integrable (fun ω => max (A ω) (0 : ℝ)) P)
    (hB : Integrable B P) (hC : Integrable C P)
    (hMeas : AEStronglyMeasurable
      (fun ω => max (A ω - B ω - C ω) (0 : ℝ)) P) :
    Integrable (fun ω => max (A ω - B ω - C ω) (0 : ℝ)) P := by
  have hI : Integrable
      (fun ω => max (A ω) (0 : ℝ) + |B ω| + |C ω|) P :=
    (hA.add hB.abs).add hC.abs
  apply hI.mono_nonneg hMeas
    (Filter.Eventually.of_forall fun ω => le_max_right _ _)
  filter_upwards with ω
  apply max_le
  · have ha := le_max_left (A ω) (0 : ℝ)
    have hb := neg_le_abs (B ω)
    have hc := neg_le_abs (C ω)
    linarith
  · have hpos : 0 ≤ max (A ω) (0 : ℝ) := le_max_right _ _
    have hb := abs_nonneg (B ω)
    have hc := abs_nonneg (C ω)
    linarith
