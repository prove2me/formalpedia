-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:53:25.889204+00:00
-- url     : https://prove2.me/submissions/fc976893-dca6-457a-ad78-99756cceb5dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_zero_origin_all_real_source_rate
import Theorems.Thm_AvramDividend_Classical_avram_integration_original_unit_separated_negative_borel_levy_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-! Original all-time rate reduces to the exact unit-horizon Borel mark rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) ∂P) =
      (T : ℝ≥0∞) * X.ν B := by
  calc
    _ = (T : ℝ≥0∞) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) :=
        avram_p2_d_future_original_zero_origin_all_real_source_rate X B hB T
    _ = (T : ℝ≥0∞) * X.ν B :=
        congrArg (fun r : ℝ≥0∞ => (T : ℝ≥0∞) * r)
          (avram_integration_original_unit_separated_negative_borel_levy_rate
            X B hB ε hε hBsep)
