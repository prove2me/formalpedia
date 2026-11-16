-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a545_C0_value_stopped_nonnegative_endpoint_AEStronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:23:47.727056+00:00
-- url     : https://prove2.me/submissions/08c53b67-c7ab-4f47-b338-56556bbd28f1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a544_positive_C0_value_Borel_extension
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (hw : ContinuousOn w (Set.Ioi (0 : ℝ)))
    (Z : Ω → ℝ) (hZm : Measurable Z)
    (hZ0 : ∀ᵐ ω ∂P, 0 ≤ Z ω) :
    AEStronglyMeasurable (fun ω => w (Z ω)) P := by
  classical
  have hext : Measurable (fun ω => if 0 < Z ω then w (Z ω) else w 0) :=
    (avram_ga_a544_positive_C0_value_Borel_extension w hw).comp hZm
  have heq : (fun ω => w (Z ω)) =ᵐ[P]
      (fun ω => if 0 < Z ω then w (Z ω) else w 0) := by
    filter_upwards [hZ0] with ω hω
    by_cases hz : 0 < Z ω
    · simp [hz]
    · have hzero : Z ω = 0 := le_antisymm (le_of_not_gt hz) hω
      simp [hzero]
  exact hext.aestronglyMeasurable.congr heq.symm
