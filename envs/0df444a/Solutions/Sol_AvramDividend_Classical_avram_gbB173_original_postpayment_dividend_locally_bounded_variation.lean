-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB173_original_postpayment_dividend_locally_bounded_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:37:50.253404+00:00
-- url     : https://prove2.me/submissions/ead8dd63-0c2c-4d7b-83cb-971c99bb45cd

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    LocallyBoundedVariationOn (fun t : ℝ≥0 => rightLimit D t ω) Set.univ := by
  exact ((avram_wave3_03_dividendStrategy_rightLimit_monotone
    D hD ω).monotoneOn Set.univ).locallyBoundedVariationOn
