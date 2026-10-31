-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_dividend_predictable_on_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:48:32.195977+00:00
-- url     : https://prove2.me/submissions/e29fd421-3f2e-4387-bafd-1e71724e2b5d

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_dividend_strategy_predictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original dividend control is predictable on the exact right-continuous
filtration where the source Lévy process is reconstructed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    @Measurable (ℝ≥0 × Ω) ℝ 𝓕.rightCont.predictable inferInstance
      (fun p => D p.1 p.2) := by
  exact avram_wave3_04_dividend_strategy_predictable
    𝓕.rightCont D (dividendStrategy_rightCont_filtration D hD)
