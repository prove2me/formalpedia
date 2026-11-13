-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a35_original_dividend_rightLimit_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:44:35.123434+00:00
-- url     : https://prove2.me/submissions/58d5e1be-46f4-4d56-be2c-445ca905d3af

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    ∀ (t : ℝ≥0) (ω : Ω), 0 ≤ rightLimit D t ω := by
  intro t ω
  have hbase : 0 ≤ D t ω := dividendStrategy_path_nonneg D hD ω t
  have hlim : D t ω ≤ rightLimit D t ω :=
    dividendStrategy_le_rightLimit D hD ω t
  exact le_trans hbase hlim
