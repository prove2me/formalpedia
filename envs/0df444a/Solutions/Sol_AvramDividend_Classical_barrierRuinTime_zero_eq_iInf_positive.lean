-- Prove2me | solution 1 for AvramDividend.Classical.barrierRuinTime_zero_eq_iInf_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:27:33.428179+00:00
-- url     : https://prove2.me/submissions/cf86ce02-3f59-418a-9f8e-728dfee5d202

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    barrierRuinTime X 0 ω =
      ⨅ ε : ℝ, ⨅ _ : 0 < ε, barrierRuinTime X ε ω := by
  unfold barrierRuinTime
  apply le_antisymm
  · exact le_iInf₂ fun ε hε => le_iInf₂ fun t ht => iInf₂_le t (hε.trans ht)
  · exact le_iInf₂ fun t ht =>
      (iInf₂_le (drawdown X t ω / 2) (half_pos ht)).trans (iInf₂_le t (by linarith : drawdown X t ω / 2 < drawdown X t ω))
