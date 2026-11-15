-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_uniform_kernel_crossing_indicator_set_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:02:13.281508+00:00
-- url     : https://prove2.me/submissions/97ca99f7-0375-414b-bec2-8a2ce2a1cfc4

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
theorem solution (y : ℝ) (hy : 0 < y) (hy1 : y < 1) :
    (∫ z in Ioo (-1 : ℝ) 0,
      (if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0)
        ∂(volume : Measure ℝ)) =
    (∫ z in Ioo (-1 : ℝ) (-y),
      -(y + (1 / 2 : ℝ) + z) ∂(volume : Measure ℝ)) := by
  have hneg : -y < (0 : ℝ) := by linarith
  have hFunc : (fun z : ℝ =>
      if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0) =
      (Iio (-y)).indicator
        (fun z : ℝ => -(y + (1 / 2 : ℝ) + z)) := by
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
  have hset : Iio (-y) ∩ Ioo (-1 : ℝ) 0 =
      Ioo (-1 : ℝ) (-y) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨hz, hlo, hhi⟩
      exact ⟨hlo, hz⟩
    · rintro ⟨hlo, hhi⟩
      exact ⟨hhi, hlo, lt_trans hhi hneg⟩
  calc
    _ = ∫ z in Ioo (-1 : ℝ) 0,
          (Iio (-y)).indicator
            (fun z : ℝ => -(y + (1 / 2 : ℝ) + z)) z
            ∂(volume : Measure ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro z hz
          exact congrFun hFunc z
    _ = ∫ z in Ioo (-1 : ℝ) (-y),
          -(y + (1 / 2 : ℝ) + z)
            ∂(volume : Measure ℝ) := by
          change (∫ z,
              (Iio (-y)).indicator
                (fun z : ℝ => -(y + (1 / 2 : ℝ) + z)) z
                ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) = _
          rw [integral_indicator measurableSet_Iio]
          change (∫ z, -(y + (1 / 2 : ℝ) + z)
            ∂(((volume : Measure ℝ).restrict
              (Ioo (-1 : ℝ) 0)).restrict (Iio (-y)))) = _
          rw [Measure.restrict_restrict measurableSet_Iio, hset]
