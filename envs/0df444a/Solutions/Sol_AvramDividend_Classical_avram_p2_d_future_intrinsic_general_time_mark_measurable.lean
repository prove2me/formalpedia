-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_intrinsic_general_time_mark_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:47:21.19801+00:00
-- url     : https://prove2.me/submissions/6f038560-4eef-495b-b03f-0be3647a4c2d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Measurability of the full original intrinsic marked jump measure on every
jointly Borel physical time-mark test set, including infinite-count sets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : Set (ℝ≥0 × ℝ)) (hC : MeasurableSet C) :
    Measurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C) := by
  classical
  obtain ⟨κ, _, hκ⟩ := avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  have hEval : Measurable (fun ω : Ω => κ ω C) :=
    (Measure.measurable_coe hC).comp (ProbabilityTheory.Kernel.measurable κ)
  simpa only [hκ] using hEval
