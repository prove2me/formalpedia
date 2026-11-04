-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_negative_band_source_rate_to_real_lintegral
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:14:25.517764+00:00
-- url     : https://prove2.me/submissions/3e6c7ff9-1de1-4ae3-b756-1791b41daab9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original marked first moment, converted to the real slope normalization. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ∂P).toReal =
    (T : ℝ) *
      (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal := by
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
    positivity
  have hSource :=
    avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
      X T (Iic (-(1 / ((n : ℝ) + 1))))
      measurableSet_Iic (1 / ((n : ℝ) + 1)) hε
      (Set.Subset.rfl)
  have hReal := congrArg ENNReal.toReal hSource
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using hReal
