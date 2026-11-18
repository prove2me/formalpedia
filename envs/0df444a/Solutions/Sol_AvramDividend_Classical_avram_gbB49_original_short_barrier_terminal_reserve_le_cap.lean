-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB49_original_short_barrier_terminal_reserve_le_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:45:56.875185+00:00
-- url     : https://prove2.me/submissions/48c7538c-3918-45b5-8475-83892fd23d88

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound_all_capital
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original positive-time barrier reserve cap upper bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ω : Ω) (hT : 0 < T)
    (hTube : ∀ s : ℝ≥0, s ≤ T → |X.X s ω| ≤ (1 / 400 : ℝ)) :
    riskProcess X (1 / 8 : ℝ)
      (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω ≤
      (1 / 8 : ℝ) := by
  have hCap :=
    barrierStrategy_reserve_cap_bound_all_capital
      X (1 / 8 : ℝ) (1 / 8 : ℝ)
      (by norm_num) (by norm_num) ω T hT
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1 / 8)).mp hCap
