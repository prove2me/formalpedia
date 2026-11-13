-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a45_original_fullcell_spatial_endpoint_ge_risk
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:54:24.684546+00:00
-- url     : https://prove2.me/submissions/aae75220-7500-4189-aa22-579472daf58d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger87_original_strict_rightlimit_le_later_dividend
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

-- In a genuinely unstraddled source cell, the prepayment reserve lies below the spatial source endpoint.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s t : ℝ≥0) (hst : s < t) :
    riskProcess X x D t ω ≤
      x + X.X t ω - rightLimit D s ω := by
  have hPay := avram_gledger87_original_strict_rightlimit_le_later_dividend
    D hD ω s t hst
  change x + X.X t ω - D t ω ≤
    x + X.X t ω - rightLimit D s ω
  linarith
