-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_drifted_preBrownian_filtered_indep
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:53:33.29019+00:00
-- url     : https://prove2.me/submissions/ca3de93c-7fed-4b14-852f-3851d927ede0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_drifted_natural_filtration_le
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_drifted_increment_future_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

/-- Brownian future increments stay independent of the drifted natural past. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω}
    (U : ℝ≥0 → Ω → ℝ)
    (hpre : IsPreBrownianReal U P)
    (hmeas : ∀ t : ℝ≥0,
      StronglyMeasurable (fun ω => U t ω - (t : ℝ)))
    (s t : ℝ≥0) (hst : s ≤ t) :
    Indep
      (MeasurableSpace.comap
        (fun ω => (U t ω - (t : ℝ)) - (U s ω - (s : ℝ)))
        inferInstance)
      ((Filtration.natural (fun t ω => U t ω - (t : ℝ)) hmeas) s)
      P := by
  have hbase :
      Indep
        (MeasurableSpace.comap
          (fun ω (r : ℝ≥0) => U (s + r) ω - U s ω)
          inferInstance)
        (MeasurableSpace.comap
          (fun ω (u : Set.Iic s) => U (u : ℝ≥0) ω)
          inferInstance) P := hpre.indepFun_shift s
  have hfut := avram_wave3_04_drifted_increment_future_measurable U s t hst
  have hpast := avram_wave3_04_drifted_natural_filtration_le U hmeas s
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left hbase hfut) hpast
