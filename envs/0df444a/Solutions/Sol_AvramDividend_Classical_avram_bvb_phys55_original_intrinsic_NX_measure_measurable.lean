-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys55_original_intrinsic_NX_measure_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T16:11:27.74711+00:00
-- url     : https://prove2.me/submissions/060642a8-1d56-4aa1-a2d8-d468bdde3092

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u)))) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  exact avram_p2_d_future_intrinsic_general_time_mark_measurable X S hS
