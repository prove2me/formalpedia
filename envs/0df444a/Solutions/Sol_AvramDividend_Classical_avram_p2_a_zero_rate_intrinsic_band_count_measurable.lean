-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_intrinsic_band_count_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:28:12.373061+00:00
-- url     : https://prove2.me/submissions/613b4032-3454-4113-b9d3-726c2400b863

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original-process intrinsic jump count on any Borel
time-mark rectangle is measurable, through its proved source kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B)) := by
  obtain ⟨κ, _, hκ⟩ :=
    avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  have hRect : MeasurableSet (Ioc 0 T ×ˢ B) :=
    measurableSet_Ioc.prod hB
  have hMeas := ProbabilityTheory.Kernel.measurable_coe κ hRect
  convert hMeas using 1
  funext ω
  exact congrArg
    (fun μ : Measure (ℝ≥0 × ℝ) => μ (Ioc 0 T ×ˢ B))
    (hκ ω).symm
