-- Prove2me | solution 1 for AvramDividend.Classical.renewal_measure_ac_on_positive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:39:36.732514+00:00
-- url     : https://prove2.me/submissions/82a52fb6-a68a-4d6c-a6bf-3cd85b76f15d

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

open MeasureTheory Set NNReal ENNReal in
theorem solution (κ R : Measure ℝ) [SFinite κ] [SFinite R]
    (hκ : κ ≪ (volume : Measure ℝ))
    (a b : ℝ≥0∞)
    (hR : R = a • (Measure.dirac (0 : ℝ)) + b • (R ∗ κ)) :
    R.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ) := by
  have hc : R ∗ κ ≪ (volume : Measure ℝ) := Measure.conv_absolutelyContinuous hκ
  refine Measure.AbsolutelyContinuous.mk (fun s hs h0 => ?_)
  rw [Measure.restrict_apply hs]
  have h1 : (R ∗ κ) (s ∩ Ioi 0) = 0 := hc (measure_mono_null inter_subset_left h0)
  have h2 : (Measure.dirac (0:ℝ)) (s ∩ Ioi 0) = 0 := by
    rw [Measure.dirac_apply' _ (hs.inter measurableSet_Ioi)]
    simp
  nth_rewrite 1 [hR]
  simp [h1, h2]
