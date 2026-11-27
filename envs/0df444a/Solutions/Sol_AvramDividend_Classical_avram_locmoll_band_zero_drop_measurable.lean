-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_zero_drop_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:33:38.758309+00:00
-- url     : https://prove2.me/submissions/dacc7e4e-54a9-4da2-816b-f5c333a3645d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_realTime_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
    let U : Set ℝ := {t : ℝ | rightLimit D t.toNNReal ω = D t.toNNReal ω}
    MeasurableSet U := by 
  dsimp only
  exact measurableSet_eq_fun
    ((avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω).measurable.comp
      measurable_real_toNNReal)
    (dividendStrategy_realTime_measurable D hD ω)
