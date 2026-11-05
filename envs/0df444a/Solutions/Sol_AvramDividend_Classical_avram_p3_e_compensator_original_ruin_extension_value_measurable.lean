-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_ruin_extension_value_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:51:49.900067+00:00
-- url     : https://prove2.me/submissions/178d189d-7095-4bd7-930c-f7b4f9380939

import Mathlib
open MeasureTheory Set
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original ruin extension is Borel measurable, allowing a boundary jump. -/
theorem solution
(w : ℝ → ℝ)
(hw_cont : ContinuousOn w (Set.Ici 0))
(hw_neg : ∀ y < 0, w y = 0) :
Measurable w := by
  have hmaxCont : Continuous (fun y : ℝ => max y 0) :=
    continuous_id.max continuous_const
  have hmaxMem (y : ℝ) : max y 0 ∈ Ici (0 : ℝ) := by
    change (0 : ℝ) ≤ max y (0 : ℝ)
    exact le_max_right y 0
  have hwplus : Continuous (fun y : ℝ => w (max y 0)) :=
    hw_cont.comp_continuous hmaxCont hmaxMem
  have heq : w = fun y : ℝ => if y < 0 then 0 else w (max y 0) := by
    funext y
    by_cases hy : y < 0
    · simp [hy, hw_neg y hy]
    · have hy0 : 0 ≤ y := le_of_not_gt hy
      simp [hy, max_eq_left hy0]
  rw [heq]
  exact (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ))).ite
    measurableSet_Iio hwplus.measurable
