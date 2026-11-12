-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB78_original_dividend_rightLimit_discontinuities_countable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:14:30.826279+00:00
-- url     : https://prove2.me/submissions/fec92ebc-0f93-4969-8795-6490dbecfcad

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Set.Countable {t : ℝ≥0 |
      ¬ ContinuousAt (fun s : ℝ≥0 => rightLimit D s ω) t} := by
  exact (avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω).countable_not_continuousAt
