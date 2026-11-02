-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_jump_time_support_lebesgue_null_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:28:23.377566+00:00
-- url     : https://prove2.me/submissions/67c1a2fc-d4ef-409b-80f1-3287d0eb52ae

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_original_levy_jump_times_countable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (νt : Measure ℝ≥0) [NullSingletonClass νt] :
    νt {t : ℝ≥0 |
      0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0} = 0 := by
  have hCount := avram_wave4_p2_all_original_levy_jump_times_countable X ω
  have hEq : {t : ℝ≥0 | 0 < t ∧ X.X t ω -
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0} =
      {t : ℝ≥0 | 0 < t ∧ X.X t ω ≠
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t} := by
    ext t
    simp only [Set.mem_setOf_eq, sub_ne_zero]
  rw [hEq]
  exact hCount.measure_zero (μ := νt)
