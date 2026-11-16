-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_uniform_crossing_kernel_integrableOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:31:36.691084+00:00
-- url     : https://prove2.me/submissions/c6592512-38ea-42e8-8eb4-c1862d93f65c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
theorem solution (y : ℝ) :
    IntegrableOn (fun z : ℝ =>
      if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0)
      (Ioo (-1 : ℝ) 0) (volume : Measure ℝ) := by
  have hcont : Continuous (fun z : ℝ => -(y + (1 / 2 : ℝ) + z)) := by
    fun_prop
  have hBase : IntegrableOn
      (fun z : ℝ => -(y + (1 / 2 : ℝ) + z))
      (Icc (-1 : ℝ) 0) (volume : Measure ℝ) :=
    hcont.integrableOn_Icc
  have hSub : Iio (-y) ∩ Ioo (-1 : ℝ) 0 ⊆ Icc (-1 : ℝ) 0 := by
    intro z hz
    exact ⟨le_of_lt hz.2.1, le_of_lt hz.2.2⟩
  have hRestrict := hBase.mono_set hSub
  have hEq : (fun z : ℝ =>
      if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0) =
      (Iio (-y)).indicator (fun z : ℝ => -(y + (1 / 2 : ℝ) + z)) := by
    funext z
    by_cases hz : y + z < 0
    · have hm : z ∈ Iio (-y) := by
        simp only [Set.mem_Iio]
        linarith
      simp [hz, hm]
    · have hm : z ∉ Iio (-y) := by
        simp only [Set.mem_Iio]
        linarith
      simp [hz, hm]
  rw [hEq]
  exact (integrableOn_indicator_iff measurableSet_Iio).2 hRestrict
