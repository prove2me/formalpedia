-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB149_original_gaussian_barrier_dividends_quantitative_drift_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:11:05.370172+00:00
-- url     : https://prove2.me/submissions/927a5817-f0a0-4ec9-a916-988511d82329

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB147_original_cap_barrier_regulator_dominates_source_at_positive_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original Gaussian cap-reflection drift lower for cumulative dividends. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ω : Ω) (B : ℝ)
    (hSource : X.X T ω = B + 2 * (T : ℝ))
    (hCentered : |B| ≤ (1 / 4000 : ℝ)) :
    2 * (T : ℝ) - (1 / 4000 : ℝ) ≤
      barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) T ω := by
  have hReg :=
    avram_gbB147_original_cap_barrier_regulator_dominates_source_at_positive_time
      X ω T hT
  have hBound := (abs_le.mp hCentered).1
  linarith
