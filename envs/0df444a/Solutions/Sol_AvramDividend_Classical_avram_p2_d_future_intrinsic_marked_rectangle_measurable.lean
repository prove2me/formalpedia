-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_intrinsic_marked_rectangle_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:27:28.062287+00:00
-- url     : https://prove2.me/submissions/b3fddbc2-6b8d-405f-8615-307d69234806

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The physical marked source rectangle has a measurable count as a function
of the original sample; no Poisson representation is used. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)) := by
  classical
  obtain ⟨κ, _, hκ⟩ := avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  have hC : MeasurableSet (Ioc s t ×ˢ B) := measurableSet_Ioc.prod hB
  have hEval : Measurable (fun ω : Ω => κ ω (Ioc s t ×ˢ B)) :=
    (Measure.measurable_coe hC).comp (ProbabilityTheory.Kernel.measurable κ)
  simpa only [hκ] using hEval
