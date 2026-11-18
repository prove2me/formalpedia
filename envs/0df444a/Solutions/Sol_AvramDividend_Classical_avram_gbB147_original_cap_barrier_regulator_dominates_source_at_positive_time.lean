-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB147_original_cap_barrier_regulator_dominates_source_at_positive_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:06:13.096875+00:00
-- url     : https://prove2.me/submissions/28107480-9d3e-4b12-a0ca-8d9cf11a0622

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound_all_capital
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original equal-cap dividend regulator dominates source at positive time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (hT : 0 < T) :
    X.X T ω ≤
      barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) T ω := by
  have hCapNN :=
    barrierStrategy_reserve_cap_bound_all_capital
      X (1 / 8 : ℝ) (1 / 8 : ℝ)
      (by norm_num) (by norm_num) ω T hT
  have hCap : riskProcess X (1 / 8 : ℝ)
      (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω ≤
      (1 / 8 : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff
      (by norm_num : (0 : ℝ) ≤ 1 / 8)).mp hCapNN
  change (1 / 8 : ℝ) + X.X T ω -
    barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) T ω ≤
    (1 / 8 : ℝ) at hCap
  linarith
